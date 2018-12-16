pragma solidity ^ 0.4 .25;

contract CTWatch {
    //curve parameters secp256r1
    uint256 constant a = 115792089210356248762697446949407573530086143415290314195533631308867097853948;
    uint256 constant b = 41058363725152142129326129780047268409114441015993725554835256314039467401291;
    uint256 constant gx = 48439561293906451759052585252797914202762949526041747995844080717082404635286;
    uint256 constant gy = 36134250956749795798585127919587881956611106672985015071877198253568414405109;
    uint256 constant p = 115792089210356248762697446949407573530086143415290314195533631308867097853951;
    uint256 constant n = 115792089210356248762697446949407573529996955224135760342422259061068512044369;
    uint256 constant h = 1;
    // log states
    // map index => copy of latest sth entry
    mapping(uint8 => LogEntry) latestSTH;
    // map index => pubkey
    mapping(uint8 => PK) keyList;
    // map index => bool, set to true if the log has been confirmed to missbehave
    mapping(uint8 => bool) missbehaving;
    address owner;

    // structure of STH
    struct STH{
        uint8 v1;
        uint8 tree_head;
        uint64 timestamp; 
        uint64 tree_size; 
        bytes32 sha256_root_hash; 
    }

    // data structures
    struct LogEntry{
        uint256 e; // maybe only save e,r,s since clients have everything else
        uint256 r;
        uint256 s;
        // uint8 v1;
        // uint8 tree_head;
        uint64 timestamp; 
        uint64 tree_size; 
        bytes32 sha256_root_hash; 
    }

    struct PK {
        uint256 qx;
        uint256 qy;
    }

    constructor() public {
        owner = msg.sender;
    }

    function addLog(uint8 logID, uint256 qx, uint256 qy) public {
        require(msg.sender == owner);
        keyList[logID] = PK(qx, qy);
        missbehaving[logID] = false;
    }

    function calculateE(uint8 v1, uint8 tree_head, uint64 timestamp, uint64 tree_size, bytes32 sha256_root_hash) public returns(uint256) {
        bytes32 hashed = sha256(abi.encodePacked(v1, tree_head, 
                                                 timestamp, tree_size,
                                                 sha256_root_hash));
        return uint256(hashed);
    }

    // sigparams = [e, r, s]
    function updateSTH(uint8 logID, uint256[3] memory sigParams, uint64 timestamp, uint64 tree_size, bytes32 sha256_root_hash) 
        public {
            require(timestamp > latestSTH[logID].timestamp && tree_size > latestSTH[logID].tree_size, "can't update to an older STH");
            require(ecdsaverify(keyList[logID].qx, keyList[logID].qy, sigParams[0], sigParams[1], sigParams[2]), "invalid STH signature");
            latestSTH[logID] = LogEntry(sigParams[0], sigParams[1], sigParams[2], timestamp, tree_size, sha256_root_hash);
    }

    // (first/second)Sig = [e, r, s]
    // (first/second)VTH = [version, tree_head]
    // (first/second)SzTs = [timestamp, tree_size]
    function proveMalicious(uint8 id, uint256[3] memory firstSig, uint256[3] memory secondSig,
                            uint8[2] memory firstVTH, uint64[2] memory firstSzTs, bytes32 firstHash,
                            uint8[2] memory secondVTH, uint64[2] memory secondSzTs, bytes32 secondHash) public {
        require(firstSzTs[0] == secondSzTs[0], "STHs are of different sizes");
        require(calculateE(firstVTH[0], firstVTH[1], firstSzTs[0], firstSzTs[1], firstHash) == firstSig[0], "First signature's e value does not match provided data");
        require(calculateE(secondVTH[0], secondVTH[1], secondSzTs[0], secondSzTs[1], secondHash) == secondSig[0], "Second signature's e value does not match provided data");
        require(firstSig[1] != secondSig[1], "r parameter is equal");
        require(firstSig[2] != secondSig[2], "s parameter is equal");
        bool first = ecdsaverify(keyList[id].qx, keyList[id].qy, firstSig[0], firstSig[1], firstSig[2]);
        bool second = ecdsaverify(keyList[id].qx, keyList[id].qy, secondSig[0], secondSig[1], secondSig[2]);
        if(first && second){
            missbehaving[id] = true;
        }
    }

    // NOTE: only checks consistency not any signatures
    // algorithm from https://github.com/google/certificate-transparency/blob/master/python/ct/crypto/merkle.py
    function verifyConsistency(uint64 old_size, uint64 new_size, bytes32 old_root, 
                               bytes32 new_root, bytes32[30] memory proof) public returns(bool){
        // require(new_size-old_size < x) maybe add check to make sure not too much gas can be used, but destroys functionality
        require(old_size < new_size, "Older tree is larger than new. Maybe wrong order of the inputs.");
        // return true if the trees are identical
        if(old_size == new_size){
            if(old_root == new_root){
                return true;
            }
        }
        // return true for consistency proof with empty tree
        if(old_size == 0) {
            return true;
        }
        // now 0 < old_size < new_size
        uint64 node = old_size-1;
        uint64 last_node = new_size-1;

        while(node % 2 == 1){
            node = node/2;
            last_node = last_node/2;
        }
        // do the actual proof stuff (without error checking)
        uint64 arr_pointer = 0;
        bytes32 old_hash;
        bytes32 new_hash;
        if(node != 0){
            new_hash = proof[arr_pointer];
            old_hash = proof[arr_pointer++];
        } else {
            new_hash = old_root;
            old_hash = old_root;
        }

        while(node != 0){
            if (node % 2 == 1){
                // node is a right child: left sibling exists in both trees.
                old_hash = hashChildren(proof[arr_pointer], old_hash);
                new_hash = hashChildren(proof[arr_pointer++], new_hash);
            }
            else if(node < last_node) {
                // node is a left child: right sibling only exists in the newer tree.
                new_hash = hashChildren(new_hash, proof[arr_pointer++]);
            }
            node = node/2;
            last_node = last_node/2;
        }
        while(last_node != 0){
            new_hash = hashChildren(new_hash, proof[arr_pointer++]);
            last_node = last_node/2;
        }
        // TODO: Maybe use require structure instead of if/elif
        if (new_hash != new_root){
            // proof is invalid, not proof of misbehaving tho
            return false;
        }
        else if(old_hash != old_root){
            // maybe mark as misbehaving(after some authenticity check) since 
            // it's proof of inconsistency
            return false;
        }
        return true;
    }

    function hashChildren(bytes32 left, bytes32 right) private returns(bytes32) {
        return sha256(abi.encodePacked(0x01, left, right));
    }

    function getLogEntry(uint8 logID) public returns(uint256, uint256, uint256, uint64, uint64, bytes32) {
        return (latestSTH[logID].e, latestSTH[logID].r, latestSTH[logID].r,
        latestSTH[logID].timestamp, latestSTH[logID].tree_size, latestSTH[logID].sha256_root_hash);
    }

    function verifySTH(uint8 id, uint256 e, uint256 r, uint256 s) public returns (bool){
        if(missbehaving[id]){
            return false;
        }
        return ecdsaverify(keyList[id].qx, keyList[id].qy, e, r, s);
    }

    function testECDSA() public returns(bool) {
        uint256 e = uint256(sha256("test")); //message
        uint256 r = 0xa5a59ee846fef2e8020bf69cf538cbd61a2b3b3745508d7239dbc094b8da0c4c; //signature
        uint256 s = 0x256db7344f3ecd13c2040542b5be5335311780b0ab024878352259c3e9a2fd4c; //signature
        uint256 qx = 0x99783cb14533c0161a5ab45bf95d08a29cd0ea8dd4c84274e2be59ad15c67696; //public key x-coordinate signer
        uint256 qy = 0x0cf0afa1074a57ac644b23479e5b3fb7b245eb4b420ef370210371a944beaceb; //public key y-coordinate signer
        return ecdsaverify(qx, qy, e, r, s);
    }

    // The rest of the code is TLS-N code from https://github.com/tls-n/tlsnutils/blob/master/contracts/ECMath.sol
    // Copyright (c) 2017 TLS-N
    function ecdsaverify(uint256 qx, uint256 qy, uint256 e, uint256 r, uint256 s) private returns(bool) {

        if (!isPoint(qx, qy)) {
            return false;
        }

        //temporary variables
        uint256 w;
        uint256 u1;
        uint256 u2;
        uint256[3] memory T1;
        uint256[3] memory T2;
        w = invmod(s, n);
        u1 = mulmod(e, w, n);
        u2 = mulmod(r, w, n);
        T1 = ecmul([gx, gy, 1], u1);
        T2 = ecmul([qx, qy, 1], u2);
        T2 = ecadd(T1, T2);
        if (r == JtoA(T2)[0]) {
            return true;
        }
        return false;
    }

    //function checks if point (x1,y1) is on curve, x1 and y1 affine coordinate parameters
    function isPoint(uint256 x1, uint256 y1) private returns(bool) {
        //point fulfills y^2=x^3+ax+b?
        if (mulmod(y1, y1, p) == addmod(mulmod(x1, mulmod(x1, x1, p), p), addmod(mulmod(a, x1, p), b, p), p)) {
            return (true);
        } else {
            return (false);
        }
    }

    // point addition for elliptic curve in jacobian coordinates
    // formula from https://en.wikibooks.org/wiki/Cryptography/Prime_Curve/Jacobian_Coordinates
    function ecadd(uint256[3] P, uint256[3] Q) private returns(uint256[3] R) {

        uint256 u1;
        uint256 u2;
        uint256 s1;
        uint256 s2;

        if (Q[0] == 0 && Q[1] == 0 && Q[2] == 0) {
            return P;
        }

        u1 = mulmod(P[0], mulmod(Q[2], Q[2], p), p);
        u2 = mulmod(Q[0], mulmod(P[2], P[2], p), p);
        s1 = mulmod(P[1], mulmod(mulmod(Q[2], Q[2], p), Q[2], p), p);
        s2 = mulmod(Q[1], mulmod(mulmod(P[2], P[2], p), P[2], p), p);

        if (u1 == u2) {
            if (s1 != s2) {
                R[0] = 1;
                R[1] = 1;
                R[2] = 0;
                return R;
            } else {
                return ecdouble(P);
            }
        }

        uint256 h;
        uint256 r;

        h = addmod(u2, (p - u1), p);
        r = addmod(s2, (p - s1), p);

        R[0] = addmod(addmod(mulmod(r, r, p), (p - mulmod(h, mulmod(h, h, p), p)), p), (p - mulmod(2, mulmod(u1, mulmod(h, h, p), p), p)), p);
        R[1] = addmod(mulmod(r, addmod(mulmod(u1, mulmod(h, h, p), p), (p - R[0]), p), p), (p - mulmod(s1, mulmod(h, mulmod(h, h, p), p), p)), p);
        R[2] = mulmod(h, mulmod(P[2], Q[2], p), p);

        return (R);
    }

    //point doubling for elliptic curve in jacobian coordinates
    //formula from https://en.wikibooks.org/wiki/Cryptography/Prime_Curve/Jacobian_Coordinates
    function ecdouble(uint256[3] P) private returns(uint256[3] R) {

        //return point at infinity
        if (P[1] == 0) {
            R[0] = 1;
            R[1] = 1;
            R[2] = 0;
            return (R);
        }

        uint256 m;
        uint256 s;

        s = mulmod(4, mulmod(P[0], mulmod(P[1], P[1], p), p), p);
        m = addmod(mulmod(3, mulmod(P[0], P[0], p), p), mulmod(a, mulmod(mulmod(P[2], P[2], p), mulmod(P[2], P[2], p), p), p), p);
        R[0] = addmod(mulmod(m, m, p), (p - mulmod(s, 2, p)), p);
        R[1] = addmod(mulmod(m, addmod(s, (p - R[0]), p), p), (p - mulmod(8, mulmod(mulmod(P[1], P[1], p), mulmod(P[1], P[1], p), p), p)), p);
        R[2] = mulmod(2, mulmod(P[1], P[2], p), p);

        return (R);

    }

    // function for elliptic curve multiplication in jacobian coordinates using Double-and-add method
    function ecmul(uint256[3] P, uint256 d) private returns(uint256[3] R) {

        R[0] = 0;
        R[1] = 0;
        R[2] = 0;

        //return (0,0) if d=0 or (x1,y1)=(0,0)
        if (d == 0 || ((P[0] == 0) && (P[1] == 0))) {
            return (R);
        }
        uint256[3] memory T;
        T[0] = P[0]; //x-coordinate temp
        T[1] = P[1]; //y-coordinate temp
        T[2] = P[2]; //z-coordiante temp

        while (d != 0) {
            if ((d & 1) == 1) { //if last bit is 1 add T to result
                R = ecadd(T, R);
            }
            T = ecdouble(T); //double temporary coordinates
            d = d / 2; //"cut off" last bit
        }

        return R;
    }

    //jacobian to affine coordinates transfomration
    function JtoA(uint256[3] P) private returns(uint256[2] Pnew) {
        uint zInv = invmod(P[2], p);
        uint zInv2 = mulmod(zInv, zInv, p);
        Pnew[0] = mulmod(P[0], zInv2, p);
        Pnew[1] = mulmod(P[1], mulmod(zInv, zInv2, p), p);
    }

    //computing inverse by using euclidean algorithm
    function invmod(uint256 a, uint p) private returns(uint256 invA) {
        uint256 t = 0;
        uint256 newT = 1;
        uint256 r = p;
        uint256 newR = a;
        uint256 q;
        while (newR != 0) {
            q = r / newR;

            (t, newT) = (newT, addmod(t, (p - mulmod(q, newT, p)), p));
            (r, newR) = (newR, r - q * newR);
        }

        return t;
    }
    // End of TLS-N code

}
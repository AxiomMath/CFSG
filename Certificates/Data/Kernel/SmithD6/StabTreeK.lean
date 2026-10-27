module

public import Certificates.Data.Kernel.SmithD6.NcK
public import Certificates.Data.Kernel.SmithD6.StabTreeData
public import Certificates.Data.Kernel.KeyTreeChunks
public import Certificates.Data.Kernel.PkTree

public section

namespace CFSG.KD.SmithD6ST

open CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Nc

@[expose] def stKeysL : List Nat :=
  [4224, 8256, 4100, 4352, 4104, 4608, 4112, 5120, 4128, 6144, 8196, 8448, 8200, 8704, 8208, 9216,
    8224, 10240, 16392, 1049088, 16896, 33024, 16400, 1049600, 17408, 65792, 16416, 1050624, 18432,
    131328, 32784, 2098176, 33792, 66048, 32800, 2099200, 34816, 131584, 65568, 4196352, 67584,
    132096]

@[expose] noncomputable def parB (x : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight 0x6996966996696996 x) 1) 1

@[expose] noncomputable def bfB (x y : Nat) : Bool :=
  (fun a b => bIf(a, bIf(b, false, true), b)) (parB (Nat.land (Nat.land x 63) (Nat.shiftRight y 6)))
    (parB (Nat.land (Nat.land y 63) (Nat.shiftRight x 6)))

@[expose] noncomputable def sglN (u w x : Nat) : Nat :=
  Nat.xor (Nat.xor x (nIf(bfB x w, u, 0))) (nIf(bfB x u, w, 0))

@[expose] noncomputable def minN (a b : Nat) : Nat := nIf(Nat.ble a b, a, b)

@[expose] noncomputable def maxN (a b : Nat) : Nat := nIf(Nat.ble a b, b, a)

@[expose] noncomputable def keyLH (lo hi : Nat) : Nat := Nat.add (Nat.mul 4096 lo) (Nat.xor lo hi)

@[expose] noncomputable def key2N (x1 x2 : Nat) : Nat :=
  keyLH (minN x1 (minN x2 (Nat.xor x1 x2))) (maxN x1 (maxN x2 (Nat.xor x1 x2)))

@[expose] noncomputable def img4N (u w bu bw : Nat) : Nat := key2N (sglN u w bu) (sglN u w bw)

@[expose] noncomputable def imgN (a b : Nat) : Nat :=
  img4N (Nat.div a 4096) (Nat.mod a 4096) (Nat.div b 4096) (Nat.mod b 4096)

@[expose] noncomputable def eqLH (lo hi k : Nat) : Bool :=
  bAnd(Nat.blt lo 4096, bAnd(Nat.blt (Nat.xor lo hi) 4096, Nat.beq (keyLH lo hi) k))

@[expose] noncomputable def eq2N (x1 x2 k : Nat) : Bool :=
  eqLH (minN x1 (minN x2 (Nat.xor x1 x2))) (maxN x1 (maxN x2 (Nat.xor x1 x2))) k

@[expose] noncomputable def eq4N (u w bu bw k : Nat) : Bool := eq2N (sglN u w bu) (sglN u w bw) k

@[expose] noncomputable def imgEqN (a b k : Nat) : Bool :=
  eq4N (Nat.div a 4096) (Nat.mod a 4096) (Nat.div b 4096) (Nat.mod b 4096) k

@[expose] noncomputable def inN (t u w x : Nat) : Nat :=
  nIf(Nat.beq t u, 1, nIf(Nat.beq t w, 1, nIf(Nat.beq t x, 1, 0)))

@[expose] noncomputable def meetN (u w x : Nat) : Nat :=
  Nat.add (Nat.add (inN 1 u w x) (inN 2 u w x)) (inN 3 u w x)

@[expose] noncomputable def rankR (r0 r1 : Nat) : Nat :=
  nIf(bAnd(Nat.beq r0 0, Nat.beq r1 0), 0,
    nIf(bIf(Nat.beq r0 0, true, bIf(Nat.beq r1 0, true, Nat.beq r0 r1)), 1, 2))

@[expose] noncomputable def rowN (b1 b2 : Bool) : Nat := Nat.add (nIf(b1, 1, 0)) (nIf(b2, 2, 0))

@[expose] noncomputable def clsMR (m r : Nat) : Nat :=
  nIf(Nat.beq m 1, nIf(Nat.beq r 0, 1, 2), nIf(Nat.beq r 0, 3, nIf(Nat.beq r 1, 4, 5)))

@[expose] noncomputable def clsUW (u w : Nat) : Nat :=
  clsMR (meetN u w (Nat.xor u w)) (rankR (rowN (bfB 1 u) (bfB 1 w)) (rowN (bfB 2 u) (bfB 2 w)))

@[expose] noncomputable def clsN (k : Nat) : Nat :=
  nIf(Nat.beq k 4098, 0, clsUW (Nat.div k 4096) (Nat.mod k 4096))

@[expose] noncomputable def stParOK (d f : Nat) : Bool :=
  bAnd(Nat.blt 0 f, bAnd(Nat.blt 0 (pkGet JST.stD 4 (Nat.pred f)),
    Nat.blt (pkGet JST.stD 4 (Nat.pred f)) d))

@[expose] noncomputable def stStepOK (k d s q : Nat) : Bool :=
  bAnd(stParOK d (KT.find q lineTree), bAnd(imgEqN s q k, Nat.beq (clsN q) (clsN k)))

@[expose] noncomputable def stRecGo (k d g : Nat) : Bool :=
  bAnd(Nat.blt 0 d, bIf(Nat.beq d 1, Nat.beq k (repKeys.getD (clsN k) 0),
    bAnd(Nat.blt g 42, stStepOK k d (stKeysL.getD g 0) (imgN (stKeysL.getD g 0) k))))

@[expose] noncomputable def stTreeGo (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k _ ih i => bAnd(stRecGo k (pkGet JST.stD 4 i) (pkGet JST.stG 6 i), ih (Nat.succ i))) l

@[expose] noncomputable def stTreeOK (c : Nat) : Bool :=
  stTreeGo (nthC J.lineKeysC c) (Nat.mul 2048 c)

end CFSG.KD.SmithD6ST

end

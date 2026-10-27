module

public import Certificates.Data.Kernel.SuzDc2.Data

public section

namespace CFSG.KD.SuzDc2

open CFSG.KC.SLD2 CFSG.KC.E64F

@[expose] noncomputable def L (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 15 (LT.lc.getD l 0) p

@[expose] def Λ : List Nat :=
  [71, 99, 1457, 2424, 2576, 2964, 3780, 4120, 4173, 4389, 4777, 4946, 4969, 5187, 5988, 6722,
    6764, 7290, 7560, 8129, 8188, 9246, 9308, 9426, 9492, 10243, 10506, 10646, 10796, 11056,
    11227, 11746, 13266, 13518, 14087, 14277, 14601, 14877, 14959, 15088, 15131, 15361, 16171,
    16233, 17493, 17665, 17772, 17948, 18677, 18933, 18974, 19399, 19580, 19682, 19951, 19985,
    20007, 20309, 21147, 21163, 21392, 21656, 22378, 22618]

@[expose] def Δ : List Nat :=
  [10447102, 24195554, 76929462, 86724073, 116616349, 143032790, 151005820, 151644355, 157921122,
    165270206, 182269303, 192252540, 193377459, 197103664, 203018030, 226747051, 228972565,
    229955433, 253409798, 260695777, 261597090, 277871948, 283836407, 315709315, 316247816,
    338174802, 351079334, 394188784, 425095971, 425460227, 454607816, 473622599]

@[expose] noncomputable def C : Dc2Ctx := ⟨22880, L, 8, 5, 6, Λ, Δ, 13, 405405, 135⟩

@[expose] noncomputable def D : Dc2Data where
  sep := J.sep
  pw := J.pw
  bo := J.bo
  R1 := J.R1
  fB := J.fB
  fC := J.fC
  fw := J.fw
  fpc := J.fpc
  fpar := J.fpar
  fvia := J.fvia
  ford := J.ford
  R2 := J.R2
  gw := J.gw
  gd := J.gd
  roots := J.roots

@[expose] noncomputable def wOK (l : Nat) (w : List Nat) : Bool :=
  (List.range 22880).all fun p => Nat.beq (L l p) (wordF L w p)

@[expose] noncomputable def shapeOK : Bool :=
  Nat.beq LT.sgw.length 4 &&
    LT.sgw.all (fun w => w.all fun l => Nat.blt 5 l && Nat.blt l 10) &&
    LT.hw.all fun l => Nat.blt l 4 || Nat.beq l 6 || Nat.beq l 7

@[expose] noncomputable def letOK : Bool :=
  wOK 8 [6, 7] && wOK 9 [6, 7, 7] && wOK 0 (LT.sgw.getD 0 []) && wOK 1 (LT.sgw.getD 1 []) &&
    wOK 2 (LT.sgw.getD 2 []) && wOK 3 (LT.sgw.getD 3 []) && wOK 5 LT.hw &&
    (List.range 22880).all fun p => Nat.beq (L 4 (L 3 p)) p

@[expose] noncomputable def sbOK : Bool :=
  CFSG.KC.SLDc.omC (fun l x => x.map fun p => bif Nat.blt p 22880 then L l p else 0)
    [0, 1, 2, 3, 4, 5] 5 SB.B SB.C SB.rows SB.par SB.via SB.ord

end CFSG.KD.SuzDc2

end

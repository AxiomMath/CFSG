module

public import Certificates.Data.Kernel.GammaUNormK
public import Certificates.Data.Kernel.IdxFourSiftK
public import Certificates.Data.Kernel.GammaUSigmaK
public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs
public import CFSG.GF2Type.Smith1979.GammaU.SigmaInputs

public section

namespace CFSG.KC.GUA

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

@[expose] noncomputable def K0P : Nat := 5577908724741807651992100829837404187664385

@[expose] noncomputable def CBP : List Nat :=
  [11217085072836628568834429907395738704289793, 11206193378392035450704116624952948378574849,
    11200747531293244315529623033498198597446657, 16423313902298533330685809123816229702934577,
    11151733876445601724380405381131139526217742]

@[expose] noncomputable def THP : Nat := 11325979737014698116079553641009599731990592

@[expose] noncomputable def B10 : List Nat := [961, 48, 9, 5, 3, 3072, 911, 576, 320, 192]

@[expose] noncomputable def XB : Nat := 1024

@[expose] noncomputable def coefB : List Nat :=
  [897, 913, 905, 901, 3072, 3074, 988, 476, 732, 860, 1024, 1056]

@[expose] noncomputable def SD0 : List Nat :=
  [0, 3072, 3, 3075, 5, 3077, 6, 3078, 9, 3081, 10, 3082, 12, 3084, 15, 3087, 48, 3120, 51, 3123,
    53, 3125, 54, 3126, 57, 3129, 58, 3130, 60, 3132, 63, 3135, 961, 4033, 962, 4034, 964, 4036,
    967, 4039, 968, 4040, 971, 4043, 973, 4045, 974, 4046, 1009, 4081, 1010, 4082, 1012, 4084, 1015,
    4087, 1016, 4088, 1019, 4091, 1021, 4093, 1022, 4094]

@[expose] noncomputable def perpB : List Nat := [1, 2, 4, 8, 48, 64, 128, 256, 512, 1024, 2048]

@[expose] noncomputable def RHO : List Nat := [12, 20, 25, 5, 2]

@[expose] noncomputable def W0 : List (List Nat) := [[28, 1], [2, 32], [1, 29]]

@[expose] noncomputable def W2 : List (List Nat) := [[28, 2], [2, 30]]

@[expose] noncomputable def W4 : List (List Nat) :=
  [[16, 2], [8, 1], [4, 32], [2, 18], [1, 9]]

@[expose] noncomputable def W5 : List (List Nat) := [[16, 4], [8, 2], [4, 20], [2, 10]]

@[expose] noncomputable def selX (l : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih m => Nat.xor (Nat.mul (Nat.mod m 2) a) (ih (Nat.div m 2))) l m

@[expose] noncomputable def par6 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih x => Nat.xor (Nat.mod x 2) (ih (Nat.div x 2))) 6 x

@[expose] noncomputable def rowsBP (imgs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ ih => Nat.add (selX imgs c) (Nat.mul 4096 ih)) coefB

@[expose] noncomputable def pmask (n : Nat) : Nat :=
  Nat.lor (Nat.land n 31) (Nat.shiftLeft (Nat.shiftRight n 6) 5)

@[expose] noncomputable def fixD (D : List Nat) (g : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun d _ ih => Nat.beq (ap12 g d) d && ih) D

@[expose] noncomputable def commD (D : List Nat) (g : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun d _ ih => (Nat.beq (Nat.xor (ap12 g d) d) 0 || Nat.beq (Nat.xor (ap12 g d) d) 3072) && ih) D

@[expose] noncomputable def perpD (B : List Nat) (g : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => memN (Nat.xor (ap12 g b) b) SD0 && ih) B

@[expose] noncomputable def vanW (W : List (List Nat)) (φ : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => Nat.beq (par6 (Nat.land φ (nthD 0 w 0))) 0 &&
      Nat.beq (par6 (Nat.land φ (nthD 0 w 1))) 0 && ih) W

@[expose] noncomputable def cntW (W : List (List Nat)) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => Nat.add ih (bif vanW W k then 1 else 0)) 32

@[expose] noncomputable def witOK (R : List Nat) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => Nat.beq (theta0N (selX R (nthD 0 w 0))) (selX R (nthD 0 w 1)) && ih) W

@[expose] noncomputable def t1OK (R : List Nat) (W : List (List Nat)) : Bool :=
  witOK R W && Nat.blt (cntW W) 16

@[expose] noncomputable def thetaOK : Bool :=
  !Nat.beq (theta0N 3072) 0 && !Nat.beq (theta0N 3072) 3072 &&
    Nat.beq (theta0N (theta0N 3072)) 48 && memN 48 d0 && Nat.beq (theta0N 48) 3072 &&
    !Nat.beq (theta0N (theta0N 48)) 3072

@[expose] noncomputable def b10OK : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => (memN b d0 || memN b (d0.map theta0N)) && ih) B10

@[expose] noncomputable def coefOK : Bool :=
  Nat.beq (lenN coefB) 12 && !f0b XB 3072 &&
    allBelow 12 fun j => Nat.beq (selX (B10 ++ [XB, theta0N XB]) (nthD 0 coefB j)) (Nat.pow 2 j)

@[expose] noncomputable def spanOK : Bool := SD0 == spanList d0

@[expose] noncomputable def notPerp (n : Nat) : Bool :=
  !Nat.beq (Nat.land (Nat.shiftRight n 4) 1) (Nat.land (Nat.shiftRight n 5) 1)

@[expose] noncomputable def perpAt (B : List Nat) : Bool :=
  allBelow 4096 fun n => notPerp n || Nat.beq (selX B (pmask n)) n

@[expose] noncomputable def perpOK : Bool := perpAt perpB

@[expose] noncomputable def kerT (TH g : Nat) : Bool :=
  guOK TH g && unitP TH g && fixD d0 g && perpD perpB g

@[expose] noncomputable def kerAt (TH K g : Nat) : Bool :=
  bif kerT TH g then Nat.beq g idP || Nat.beq g K else true

@[expose] noncomputable def candB (y : Nat) : Nat := rowsBP (B10 ++ [y, theta0N y])

@[expose] noncomputable def kerOK (TH K : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun d _ ih => kerAt TH K (candB (Nat.xor XB d)) && ih)
    SD0

@[expose] noncomputable def inT (TH g : Nat) : Bool :=
  guOK TH g && Nat.beq (ap12 g 3072) 3072 && commD d0 g && perpD perpB g

@[expose] noncomputable def genTOK (TH : Nat) : Bool :=
  inT TH K0P && fixD d0 K0P && Nat.beq (lenN CBP) 5 &&
    List.rec (motive := fun _ => Bool) true (fun g _ ih => inT TH g && ih) CBP

@[expose] noncomputable def commAt (G : List Nat) (g : Nat) : Bool :=
  Nat.beq (mulP g g) idP &&
    List.rec (motive := fun _ => Bool) true (fun h _ ih => Nat.beq (mulP g h) (mulP h g) && ih) G

@[expose] noncomputable def commOK : Bool :=
  List.rec (motive := fun _ => Bool) true (fun g _ ih => commAt (K0P :: CBP) g && ih) (K0P :: CBP)

@[expose] noncomputable def rhoL (L : List Nat) (g : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun d _ ih => Nat.add (bif Nat.beq (Nat.xor (ap12 g d) d) 3072 then 1 else 0) (Nat.mul 2 ih)) L

@[expose] noncomputable def rhoOK : Bool :=
  Nat.beq (lenN RHO) 5 &&
    allBelow 5 (fun i => Nat.beq (rhoL [961, 48, 9, 5, 3] (nthD 0 CBP i)) (nthD 0 RHO i)) &&
    allBelow 31 fun m => !Nat.beq (selX RHO (Nat.succ m)) 0

@[expose] noncomputable def pinOK : Bool :=
  Nat.beq K0P (CFSG.KC.IF4R.packR k0) && CBP == cBasis.map CFSG.KC.IF4R.packR &&
    Nat.beq THP (CFSG.KC.IF4R.packR SigmaP.thetaRows) && GUS.rowsOK k0.toList &&
    (cBasis.all fun r => GUS.rowsOK r.toList) && GUS.rowsOK SigmaP.thetaRows.toList

end CFSG.KC.GUA

end

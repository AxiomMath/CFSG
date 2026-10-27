module

public import Certificates.Data.Kernel.IdxFourSiftK

public section

namespace CFSG.KC.GUC

open CFSG.KC.IF4C CFSG.KC.IF4R

@[expose] noncomputable def five (CG c : Nat) : List Nat :=
  [look CG (Nat.mul 5 c), look CG (Nat.add (Nat.mul 5 c) 1), look CG (Nat.add (Nat.mul 5 c) 2),
    look CG (Nat.add (Nat.mul 5 c) 3), look CG (Nat.add (Nat.mul 5 c) 4)]

@[expose] noncomputable def cjOK (v vi : Nat) (H : List Nat) (gs ms : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun ms => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ms)
    (fun g _ ih ms => List.rec (motive := fun _ => Bool) false
      (fun m ms' _ => Nat.beq (mulP v (mulP g vi)) (subP H m) && ih ms') ms) gs ms

section
variable (CS CSI FT FTi FC CG LB DP NC N : Nat)

@[expose] noncomputable def edgeOK (X k p : Nat) (ms : List Nat) : Bool :=
  cjOK (mulP (look FTi X) (mulP (look CS k) (look FT p)))
    (mulP (look FTi p) (mulP (look CSI k) (look FT X))) (five CG (fld FC X)) (five CG (fld FC p)) ms

@[expose] noncomputable def entOK (X : Nat) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) (Nat.beq (fld LB X) X)
    (fun k r _ => List.rec (motive := fun _ => Bool) false
      (fun p ms _ => Nat.blt k NC && Nat.blt p N && Nat.blt (fld DP p) (fld DP X) &&
        Nat.beq (fld LB p) (fld LB X) && edgeOK CS CSI FT FTi FC CG X k p ms) r) e

@[expose] noncomputable def entsOK (es : List (List Nat)) (X : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih X => entOK CS CSI FT FTi FC CG LB DP NC N X e && ih (Nat.succ X)) es X

end

@[expose] noncomputable def labOK (LB N : Nat) (OR : List Nat) (AR : Nat) : Bool :=
  allBelow N fun X => memN (fld LB X) OR || Nat.beq (fld LB X) AR

@[expose] noncomputable def cnOK (CS CSI TH : Nat) (L : List Nat) (CN : List (List Nat)) (k : Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih k => List.rec (motive := fun _ => Bool) false
      (fun t ms _ =>
        cjOK (look CS k) (look CSI k) L L ms &&
          ((Nat.beq t 32 && Nat.beq (mulP (look CS k) TH) (mulP TH (look CS k))) ||
            (Nat.blt t 32 &&
              Nat.beq (mulP (mulP (look CS k) TH) (mulP (look CSI k) TH)) (subP L t)))) e &&
      ih (Nat.succ k)) CN k

@[expose] noncomputable def candOK (CG FT FTi FC TH i X G : Nat) : Bool :=
  allBelow 5 (fun l => Nat.beq (look G l) (look CG (Nat.add (Nat.mul 5 i) l))) &&
    allBelow 5 (fun l => Nat.beq (look G (Nat.add 5 l))
      (mulP (look FT X) (mulP (look CG (Nat.add (Nat.mul 5 (fld FC X)) l)) (look FTi X)))) &&
    Nat.beq (look G 10) TH

@[expose] noncomputable def inO (VT PS N y : Nat) : Bool :=
  Nat.blt (fld PS y) N && Nat.beq (fld VT (fld PS y)) y

section
variable (G n VT PS N : Nat)

@[expose] noncomputable def treeOK (es : List (List Nat)) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih j => Nat.blt (nthD 0 e 0) j && Nat.blt (nthD 0 e 1) n &&
      Nat.beq (ap12 (look G (nthD 0 e 1)) (fld VT (nthD 0 e 0))) (fld VT j) && ih (Nat.succ j)) es j

@[expose] noncomputable def clOK (x : Nat) : Bool :=
  allBelow n fun g => inO VT PS N (ap12 (look G g) x)

@[expose] noncomputable def orbOK (p : Nat) (E : List (List Nat)) : Bool :=
  Nat.beq (fld VT 0) p && Nat.beq (Nat.succ (lenN E)) N &&
    allBelow N (fun j => Nat.beq (fld PS (fld VT j)) j) && treeOK G n VT E 1 &&
    allBelow N (fun j => clOK G n VT PS N (fld VT j))

end

end CFSG.KC.GUC

end

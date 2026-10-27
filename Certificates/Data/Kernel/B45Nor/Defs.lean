module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3F2
public import Mathlib

public section

namespace CFSG.KC.B45Nor

open CFSG.QuasithinUnique.Setup.X3E (dotb)

@[expose] noncomputable def papK (cs : List ℕ) (v : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun c _ ih v => Nat.xor (bif Nat.beq (Nat.land v 1) 1 then c else 0)
      (ih (Nat.shiftRight v 1))) cs v

@[expose] noncomputable def wapK (cols : Bool → List ℕ) (w : List Bool) (v : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) v (fun b _ ih => papK (cols b) ih) w

@[expose] noncomputable def wTK (ht : Bool → List ℕ) (w : List Bool) (y : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun y => y) (fun b _ ih y => ih (papK (ht b) y)) w y

@[expose] noncomputable def sumW (cols : Bool → List ℕ) (aW : List (List Bool)) (v : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.xor (wapK cols w v) ih) aW

@[expose] noncomputable def aCK (d : ℕ) (cols : Bool → List ℕ) (aW : List (List Bool)) :
    List ℕ :=
  (List.range d).map fun k => sumW cols aW (1 <<< k)

@[expose] noncomputable def rowK (cs : List ℕ) (i : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun c _ ih => Nat.add (Nat.land (Nat.shiftRight c i) 1) (Nat.mul 2 ih)) cs

@[expose] noncomputable def allIx (p : ℕ → ℕ → Bool) (xs : List ℕ) (i : ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun x _ ih i => p i x && ih (Nat.succ i)) xs i

@[expose] noncomputable def idChk (xs : List ℕ) (i : ℕ) : Bool :=
  allIx (fun i x => Nat.beq x (1 <<< i)) xs i

@[expose] noncomputable def trChk (cs hs : List ℕ) (i : ℕ) : Bool :=
  allIx (fun i h => Nat.beq h (rowK cs i)) hs i

@[expose] noncomputable def aChk (d : ℕ) (rC : List ℕ) (T psi : ℕ) (aC : List ℕ) : Bool :=
  allIx (fun k a => (Nat.beq ((1 <<< k) ^^^ papK rC a) 0 || Nat.beq ((1 <<< k) ^^^ papK rC a) T) &&
    !dotb d psi a) aC 0

@[expose] noncomputable def norKP (d : ℕ) (cols ht : Bool → List ℕ) (aW : List (List Bool))
    (T : ℕ) (gw : List (List Bool)) (masks : List ℕ) (psi : ℕ) (dw : List (List Bool))
    (rC minv : List ℕ) : Bool :=
  Nat.beq (cols false).length d && Nat.beq (cols true).length d &&
    Nat.beq (ht false).length d && Nat.beq (ht true).length d &&
    allIx (fun _ c => Nat.blt c (2 ^ d)) (cols false) 0 &&
    allIx (fun _ c => Nat.blt c (2 ^ d)) (cols true) 0 &&
    Nat.beq rC.length d && Nat.beq minv.length d && Nat.beq masks.length d &&
    Nat.beq dw.length d && Nat.blt 0 T && Nat.blt T (2 ^ d) &&
    aChk d rC T psi (aCK d cols aW) &&
    Nat.beq (sumW cols aW T) 0 &&
    idChk (masks.map (papK (gw.map fun w => wapK cols w T))) 0 &&
    idChk ((List.range d).map fun k => papK minv (rowK (dw.map fun w => wTK ht w psi) k)) 0

end CFSG.KC.B45Nor

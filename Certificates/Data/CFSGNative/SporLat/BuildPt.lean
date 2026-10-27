module

public import Certificates.Data.CFSGNative.SporLat.Build

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

def buildLatPt (n : Nat) (ta tb : Array Nat) (Δ : List Nat) (sTabs : List (Array Nat))
    (cap : Nat) : LatData (List Nat) :=
  buildLat ptAct n ta tb Δ sTabs cap

def buildO2Pt (D : LatData (List Nat)) : Array (OmegaData (List (List Nat))) :=
  buildO2 ptAct D

def omegaSpecPtB (letters : Array (Array Nat)) (Δ : List Nat) (O : OmegaData (List Nat)) : Bool :=
  decide (O.lbl[0]! = Δ) && decide (0 < O.lbl.size) &&
  decide (∀ l < letters.size, ∀ i < O.lbl.size,
    (O.pn[l]!)[i]! < O.lbl.size ∧ O.lbl[(O.pn[l]!)[i]!]! = ptAct letters[l]! O.lbl[i]!) &&
  decide (∀ i < O.lbl.size, 0 < i → O.par[i]! < i ∧ O.via[i]! < letters.size ∧
    (O.pn[O.via[i]!]!)[O.par[i]!]! = i) &&
  @distinctB (List Nat) instBEqOfDecidableEq _ O.lbl

theorem omegaSpecPtB_iff {letters : Array (Array Nat)} {Δ : List Nat} {O : OmegaData (List Nat)} :
    omegaSpecPtB letters Δ O = true ↔ OmegaSpec ptAct letters Δ O := by
  simp only [omegaSpecPtB, OmegaSpec, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

local instance omegaSpecPtDec (letters : Array (Array Nat)) (Δ : List Nat)
    (O : OmegaData (List Nat)) : Decidable (OmegaSpec ptAct letters Δ O) :=
  decidable_of_iff (omegaSpecPtB letters Δ O = true) omegaSpecPtB_iff

local instance atomOKPtDec (Δ : List Nat) (D : LatData (List Nat)) (i : Nat)
    (d : AtomData (List Nat)) (L : List (Array Nat)) : Decidable (AtomOK' ptAct Δ D i d L) := by
  unfold AtomOK'; infer_instance

local instance atomsOKPtDec (n : Nat) (ta tb : Array Nat) (Δ : List Nat)
    (D : LatData (List Nat)) : Decidable (AtomsOK ptAct n ta tb Δ D) := by
  unfold AtomsOK; infer_instance

local instance latOKPtDec (n : Nat) (ta tb : Array Nat) (Δ : List Nat)
    (D : LatData (List Nat)) : Decidable (LatOK ptAct n ta tb Δ D) := by
  unfold LatOK; infer_instance

def latOKPt (n : Nat) (ta tb : Array Nat) (Δ : List Nat) (D : LatData (List Nat)) : Bool :=
  decide (LatOK ptAct n ta tb Δ D)

theorem latOKPt_iff {n : Nat} {ta tb : Array Nat} {Δ : List Nat} {D : LatData (List Nat)} :
    latOKPt n ta tb Δ D = true ↔ LatOK ptAct n ta tb Δ D :=
  decide_eq_true_iff

def o2OKPt (D : LatData (List Nat)) (Ot : Array (OmegaData (List (List Nat)))) : Bool :=
  decide (O2OK ptAct D Ot)

theorem o2OKPt_iff {D : LatData (List Nat)} {Ot : Array (OmegaData (List (List Nat)))} :
    o2OKPt D Ot = true ↔ O2OK ptAct D Ot :=
  decide_eq_true_iff

def inclPt (Δ : List Nat) (D : LatData (List Nat)) (J : Nat) (incl : List (List Nat)) : Bool :=
  decide (∀ j < J, ∀ jj < J, (GensIn ptAct Δ D j jj ↔ jj ∈ incl[j]!))

theorem inclPt_iff {Δ : List Nat} {D : LatData (List Nat)} {J : Nat} {incl : List (List Nat)} :
    inclPt Δ D J incl = true ↔ ∀ j < J, ∀ jj < J, (GensIn ptAct Δ D j jj ↔ jj ∈ incl[j]!) :=
  decide_eq_true_iff

end CFSG.QuasithinUnique.Ch1.SporLat

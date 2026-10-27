module

public import Certificates.Data.G23RecogGlueInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23.HFactsData

@[expose] def gA (i : Fin 5) : ↥Hc := ⟨gen i, Subgroup.subset_closure (Set.mem_range_self i)⟩

@[expose] def Lx (x : ↥Hc) : List ℕ := Lst x.1

@[expose] def gensOf (ss : List ↥Hc) : List (List ℕ) := ss.map Lx ++ ss.map fun s => Lx s⁻¹

@[expose] def cl (ss : List ↥Hc) : List (List ℕ) := bfsAux 576 mulL (gensOf ss) 600 [idL] [idL]

abbrev F5Eq : Prop := ∀ i : Fin 5, f5 (Fin.cast len5.symm i) = gen i

@[expose] def zA : ↥Hc := (gA 0 * gA 1) ^ 2

@[expose] def sH1 : List ↥Hc := [gA 0, gA 1]

@[expose] def sH2 : List ↥Hc := [gA 2, gA 3]

@[expose] def sK : List ↥Hc := [gA 0, gA 1, gA 2, gA 3]

@[expose] def sP : List ↥Hc := [gA 0, gA 2]

@[expose] def sC1 : List ↥Hc := [gA 0, gA 2, gA 3]

@[expose] def sC2 : List ↥Hc := [gA 2, gA 0, gA 1]

@[expose] def sN1 : List ↥Hc := [gA 0, gA 2, gA 3, gA 4]

@[expose] def sN2 : List ↥Hc := [gA 2, gA 0, gA 1, gA 4]

@[expose] def sPZ : List ↥Hc := [gA 0, gA 2, zA]

@[expose] def sPE : List ↥Hc := [gA 0, gA 2, gA 4, zA]

@[expose] def sL1 : List ↥Hc := [gA 0, zA]

@[expose] def sL2 : List ↥Hc := [gA 2, zA]

@[expose] def sT1 : List ↥Hc := [gA 0, gA 1, gA 4]

@[expose] def sT2 : List ↥Hc := [gA 2, gA 3, gA 4]

abbrev ClosedAt (ss : List ↥Hc) : Prop :=
  idL ∈ cl ss ∧ ∀ l ∈ cl ss, ∀ g ∈ gensOf ss, mulL l g ∈ cl ss

abbrev CentOK (u : ↥Hc) (ss : List ↥Hc) : Prop :=
  (∀ l ∈ elts, mulL (Lx u) l = mulL l (Lx u) → l ∈ cl ss) ∧
    ∀ s ∈ ss, mulL (Lx u) (Lx s) = mulL (Lx s) (Lx u)

abbrev Cent2OK (u v : ↥Hc) (ss : List ↥Hc) : Prop :=
  (∀ l ∈ elts, mulL (Lx u) l = mulL l (Lx u) → mulL (Lx v) l = mulL l (Lx v) → l ∈ cl ss) ∧
    ∀ s ∈ ss, mulL (Lx u) (Lx s) = mulL (Lx s) (Lx u) ∧ mulL (Lx v) (Lx s) = mulL (Lx s) (Lx v)

abbrev NormSetOK (sA ss : List ↥Hc) : Prop :=
  (∀ l ∈ elts, (∀ p ∈ sA, ∃ d ∈ cl sA, mulL l (Lx p) = mulL d l) → l ∈ cl ss) ∧
    ∀ s ∈ ss, ∀ p ∈ sA, ∃ d ∈ cl sA, mulL (Lx s) (Lx p) = mulL d (Lx s)

abbrev CentInOK (u : ↥Hc) (sA sB : List ↥Hc) : Prop :=
  (∀ l ∈ cl sA, mulL (Lx u) l = mulL l (Lx u) → l ∈ cl sB) ∧
    ∀ s ∈ sB, mulL (Lx u) (Lx s) = mulL (Lx s) (Lx u) ∧ Lx s ∈ cl sA

abbrev DisjOK (u : ↥Hc) (ss : List ↥Hc) : Prop :=
  ∀ l ∈ cl ss, l ∈ cl [u] → l = idL

abbrev InvertOK (u v : ↥Hc) : Prop :=
  ∀ l ∈ elts, mulL (Lx u) l = mulL l (Lx u) → mulL l (Lx v) ≠ mulL (Lx v⁻¹) l

abbrev ConjOK (ss : List ↥Hc) : Prop :=
  ∃ l ∈ cl ss, mulL l (Lx (gA 4)) = mulL (mulL (Lx (gA 4)) (Lx zA)) l

abbrev InvKOK : Prop :=
  ∀ l ∈ cl sK, (mulL l l = idL ∧ l ≠ idL ∧ l ≠ Lx zA) →
    ∀ l' ∈ cl sK, (mulL l' l' = idL ∧ l' ≠ idL ∧ l' ≠ Lx zA) →
      ∃ h ∈ elts, mulL h l = mulL l' h

abbrev CardCentT : Prop :=
  (elts.filter fun l => decide (mulL (Lx (gA 4)) l = mulL l (Lx (gA 4)))).length = 8

abbrev PFacts : Prop :=
  (cl sP).length = 9 ∧ (cl sP).Nodup ∧ (∀ l ∈ cl sP, mulL l (mulL l l) = idL) ∧
    ∀ l ∈ cl sP, ∀ l' ∈ cl sP, mulL l l' = mulL l' l

end CFSG.GH74.QTGen4.Recog.G23.HFactsData

end

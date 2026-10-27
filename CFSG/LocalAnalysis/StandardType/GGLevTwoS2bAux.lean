module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem

theorem levTwoS2b_cl_mono {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    (hR : TauCeti.IsFiniteType R) {S T : Set (ι → ℤ)} (h : S ⊆ T) {β : ι → ℤ}
    (hβ : Cl hR S β) : Cl hR T β := by
  induction hβ with
  | base hb => exact Cl.base (h hb)
  | refl ha hb iha ihb => exact Cl.refl iha ihb

theorem levTwoS2b_cl_eq_of_subset {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    (hR : TauCeti.IsFiniteType R) {Φ S S' : Set (ι → ℤ)} (hS' : S' ⊆ S)
    (h : ∀ β ∈ S, Cl hR (Φ ∪ S') β) :
    Cl hR (Φ ∪ S) = Cl hR (Φ ∪ S') := by
  funext β
  apply propext
  constructor
  · intro hβ
    induction hβ with
    | base hb =>
        rcases hb with hb | hb
        · exact Cl.base (Or.inl hb)
        · exact h _ hb
    | refl ha hb iha ihb => exact Cl.refl iha ihb
  · intro hβ
    exact levTwoS2b_cl_mono hR (Set.union_subset_union (Set.Subset.refl Φ) hS') hβ

end CFSG.StandardType.LevTwo

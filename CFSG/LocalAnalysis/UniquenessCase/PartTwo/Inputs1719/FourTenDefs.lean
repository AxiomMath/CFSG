module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

structure FourTenSetting (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p e : ℕ) : Prop where
  normal : L.Normal
  fstar_eq : Fstar (⊤ : Subgroup Q) = L
  prime : p.Prime
  ne_two : p ≠ 2
  isL2 : F6.IsL2 p e ↥L
  three_lt : 3 < p ^ e
  sup_eq_top : ∃ T : Subgroup Q, IsSylowIn 2 T ⊤ ∧ L ⊔ T = ⊤
  not_isAlt_five : ¬ IsAlt ↥L 5
  not_small : ¬ (F6.IsL2 7 1 Q ∨ F6.IsL2 3 2 Q ∨ IsSymGp Q 6)

@[expose] def W4Lem4_10F : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p e : ℕ), FourTenSetting Q L p e →
    InFGroup 1 Q

@[expose] def W4Lem4_10Small : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], (F6.IsL2 7 1 Q ∨ F6.IsL2 3 2 Q ∨ IsSymGp Q 6) →
    InEGroup 1 Q

theorem w4Lem4_10_of (hF : W4Lem4_10F) (hS : W4Lem4_10Small) : W4Lem4_10 := by
  intro Q _ _ L T q hLn hFs ⟨p, e, hp, hp2, hq, hL⟩ hq3 _ hT hLT
  by_cases h5 : IsAlt ↥L 5
  · exact Or.inr (Or.inl h5)
  by_cases hs : F6.IsL2 7 1 Q ∨ F6.IsL2 3 2 Q ∨ IsSymGp Q 6
  · exact Or.inr (Or.inr ⟨hs, hS Q hs⟩)
  subst hq
  exact Or.inl (hF Q L p e ⟨hLn, hFs, hp, hp2, hL, hq3, ⟨T, hT, hLT⟩, h5, hs⟩)

@[expose] def FourTenCase (P : ℕ → ℕ → Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p e : ℕ), FourTenSetting Q L p e →
    P p e → ∀ T : Subgroup Q, IsSylowIn 2 T ⊤ → ∀ Ω : Set (Subgroup Q), IsOmegaColl Ω →
      (∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A) → genEi 1 T Ω ⊔ T = ⊤

abbrev FourTenLarge : Prop := FourTenCase fun p e => 3 ≤ e ∨ (e = 2 ∧ 5 ≤ p)

abbrev FourTenPrime : Prop := FourTenCase fun p e => e = 1 ∧ 7 ≤ p

abbrev FourTenNine : Prop := FourTenCase fun p e => p = 3 ∧ e = 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

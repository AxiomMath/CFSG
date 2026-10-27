module

public import CFSG.LocalAnalysis.StandardType.GGOrthFramePairs
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCharSum

public section

namespace CFSG.StandardType.OrthTorus

open CFSG.GroupTheory.WeirSylow

private theorem OrthWeakFrame.false_of_wrong_witt {G : Type} [Group G] {p : ℕ}
    {Bs L : Subgroup G} (Φ : OrthWeakFrame p Bs L)
    (hwrong : (IsPlusType Φ.Q ∧ Odd Φ.r) ∨ (¬ IsPlusType Φ.Q ∧ Even Φ.r)) : False := by
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have hdim := Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix
  have hsum := charSum_top_modEq_neg_one_of_witt hQ (le_trans (by decide : 1 ≤ 4) Φ.hr)
    hdim Φ.hpq hwrong
  obtain ⟨v, hv, hfix⟩ := Φ.Δ.exFixed hsum
  exact hv (Φ.hfix v hfix)

theorem OrthWeakFrame.wittType {G : Type} [Group G] {p : ℕ}
    {Bs L : Subgroup G} (Φ : OrthWeakFrame p Bs L) :
    (IsPlusType Φ.Q ∧ Even Φ.r) ∨ (¬ IsPlusType Φ.Q ∧ Odd Φ.r) := by
  classical
  by_cases he : Even Φ.r
  · by_cases hplus : IsPlusType Φ.Q
    · exact Or.inl ⟨hplus, he⟩
    · exact (Φ.false_of_wrong_witt (Or.inr ⟨hplus, he⟩)).elim
  · have ho : Odd Φ.r := Nat.not_even_iff_odd.mp he
    by_cases hplus : IsPlusType Φ.Q
    · exact (Φ.false_of_wrong_witt (Or.inl ⟨hplus, ho⟩)).elim
    · exact Or.inr ⟨hplus, ho⟩

end CFSG.StandardType.OrthTorus

end

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCClose
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCParab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.false_of_permuting_three_of_good (h : S16gRowCtx D V₀ V L hV)
    (h3 : 3 ∈ D.sig) (hm : MBarGT D.M V₀ V 2) {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hY3 : IsPGroup 3 ↥Y) (hYexp : ∀ y ∈ Y, y ^ 3 = 1) (hYnc : ¬ IsCyclic ↥Y)
    (hperm : Permutes Y D.T)
    (hcase : V₀ ≠ ⊥ ∨ 9 < Nat.card ↥Y ∨
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False := by
  by_cases hV₀ : V₀ = ⊥
  · rcases hcase with hne | hbig | ⟨v, hvV, hvT, hvC⟩
    · exact absurd hV₀ hne
    · exact h.false_of_permuting_three h3 hm hYM hY3 hYexp hYnc hperm (Or.inr hbig)
    · exact h.false_of_permuting_three_good h3 hV₀ hm hYM hY3 hYnc hperm hvV hvT hvC
  · exact h.false_of_permuting_three h3 hm hYM hY3 hYexp hYnc hperm (Or.inl hV₀)

theorem S16gRowCtx.false_of_parabolic (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hm : MBarGT D.M V₀ V 2) (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k)
    {J : Subgroup (MulAut (Vtil V₀ V hV))} {a : ℕ} (hTJ : barSub V₀ V hV D.T ≤ J)
    (hJL : J ≤ lBar V₀ V hV L ⊔ barSub V₀ V hV D.T)
    (hJcard : Nat.card ↥J = 3 ^ a * Nat.card ↥(barSub V₀ V hV D.T))
    (hJexp : ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1) (ha : 2 ≤ a)
    (hcase : V₀ ≠ ⊥ ∨ 3 ≤ a ∨
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False := by
  obtain ⟨Y, hYM, hY3, hYcard, hYexp, hYnc, hperm⟩ :=
    h.exists_permuting_of_parabolic hsimple hmult hTJ hJL hJcard hJexp ha
  refine h.false_of_permuting_three_of_good h3 hm hYM hY3 hYexp hYnc hperm ?_
  rcases hcase with hne | ha3 | hgood
  · exact Or.inl hne
  · refine Or.inr (Or.inl ?_)
    rw [hYcard]
    calc 9 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
  · exact Or.inr (Or.inr hgood)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

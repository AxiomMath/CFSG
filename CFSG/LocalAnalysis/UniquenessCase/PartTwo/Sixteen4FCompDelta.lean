module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDelta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def K_NonthinFixHalfRows : Prop :=
  (∀ (X : Type) [CommGroup X] [Finite X], (∀ x : X, x ^ 2 = 1) →
    ∀ L : Subgroup (MulAut X), CFSG.Open.IsQuasisimple ↥L →
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L) →
      SumOfAtMostThreeNat L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) →
      3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L)) ∧
  (∀ (X : Type) [CommGroup X] [Finite X], (∀ x : X, x ^ 2 = 1) →
    ∀ (L : Subgroup (MulAut X)) (m : ℕ), CFSG.Open.IsQuasisimple ↥L →
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L) →
      commSub ⊤ L ∈ irrSet L →
      Conc4_135 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) m →
      3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L))

theorem s16f_delta_lt_of_nonthin (hK : K_NonthinFixHalfRows) (D : Data G)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L))
    (hγ : 4 ≤ gamma15 D.M V₀ V h.hyp151.isElemAbelian L) :
    delta15 D.M V₀ V h.hyp151.isElemAbelian L <
      gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1 := by
  have hV := h.hyp151.isElemAbelian
  by_cases h0 : V₀ = ⊥
  · subst h0
    obtain ⟨t, -, -, -, -, hW⟩ := hc
    rcases hW.2.2 with h133 | ⟨K, -, g, -, -, -, htens⟩ | ⟨hcomp, hsum, -⟩ |
      ⟨hirr, -, hcomp, h135⟩
    · have hz := s16h_delta15_eq_zero_of_inf_fixV D hV rfl
        (s16c167_wTil_inf_fixV_eq_bot_of_odd hV L (s16h_odd_card_of_conc4_133 h133))
      omega
    · have hfix : wTil ⊥ V hV L ⊓ fixV (lBar ⊥ V hV L) = ⊥ := by
        rcases htens with ⟨-, ht⟩ | ⟨-, ht⟩ | ⟨-, ht⟩
        · exact s16h_commSub_inf_fixV_eq_bot_of_tensor (by norm_num) ht
        · exact s16h_commSub_inf_fixV_eq_bot_of_tensor (by norm_num) ht
        · exact s16h_commSub_inf_fixV_eq_bot_of_tensor (by norm_num) ht
      have hz := s16h_delta15_eq_zero_of_inf_fixV D hV rfl hfix
      omega
    · exact delta15_lt_of_fix_half D h.hyp151
        (hK.1 (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV) (lBar ⊥ V hV L)
          hcomp.2.2 hnt hsum)
        (by omega)
    · exact delta15_lt_of_fix_half D h.hyp151
        (hK.2 (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV) (lBar ⊥ V hV L) _
          hcomp.2.2 hnt hirr h135)
        (by omega)
  · exact s16c34_delta_lt_gamma_of_ne_bot D h h0 hγ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

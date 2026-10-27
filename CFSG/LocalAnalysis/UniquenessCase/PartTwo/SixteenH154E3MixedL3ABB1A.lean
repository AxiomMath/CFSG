module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB1AB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_two_rank_normalizer_W
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    {k : ℕ}
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) k)
    (hk : k ≤ 2)
    (hZbig : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hdim : k = 2 ∧ rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) = 2)
    {τ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hτ : τ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτn : τ ∈ Subgroup.normalizer (lBar ⊥ V h.hyp151.isElemAbelian L :
      Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))) :
    4 ≤ rk ↥(commSub (commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian))
      (lBar ⊥ V h.hyp151.isElemAbelian L)) (Subgroup.zpowers τ)) := by
  have hpow : ∀ w : Vtil ⊥ V h.hyp151.isElemAbelian, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one ⊥ V h.hyp151.isElemAbelian
  have hL3' : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2 := by
    have h := hL3
    rw [hdim.1] at h
    exact h
  by_cases hτC : τ ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
  · exfalso
    refine h.hyp16.not_gt
      (s16h_e3_mbar_of_rank D h.hyp16.hyp125 (n := 3) ?_ ⟨t, ht, ht2, ht1⟩)
    intro σ hσ hσ2 hσ1
    have h4 := s16h_e3_l3_two_all_involution_rank D S h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
      hL3 hk hZbig hdim hσ hσ2 hσ1
    rw [card_eq_two_pow hpow]
    exact Nat.pow_le_pow_right (by norm_num) h4
  · exact s16h_e3_l3_two_rank_normalizer_of_not_central_aux hpow ht ht2 ht1 htr hW hcomp hthin hZ
      hL3' hdim.2 hτ hτ2 hτ1 hτn hτC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

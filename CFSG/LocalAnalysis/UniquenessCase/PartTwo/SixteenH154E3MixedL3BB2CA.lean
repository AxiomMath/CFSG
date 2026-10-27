module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_three_ne_bot_dim_le_two_involution_rank
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
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hd2 : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2)
    {τ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hτ : τ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1) :
    3 ≤ rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian))
      (Subgroup.zpowers τ)) := by
  by_cases hτN : τ ∈ Subgroup.normalizer (lBar ⊥ V h.hyp151.isElemAbelian L :
      Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
  · exact s16h_e3_l3_three_ne_bot_dim_le_two_involution_rank_normalizer D S h hs2 ht ht2 ht1
      htr hW hcomp hthin hZ hL3 hd2 hτ hτ2 hτ1 hτN
  · exact s16h_e3_l3_three_ne_bot_dim_le_two_involution_rank_not_normalizer D S h hs2 ht ht2
      ht1 htr hW hcomp hthin hZ hL3 hd2 hτ hτ2 hτ1 hτN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

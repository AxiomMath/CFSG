module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAABAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAABAAB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_central_conj_comm_rank_of_not_normalizer
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∈ centSub (commSub ⊤ L))
    {g : MulAut W} (hg : g ∈ A)
    (hgN : g ∉ normalizer (L : Set (MulAut W)))
    (hne : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥) :
    3 ≤ rk ↥(commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ)) := by
  by_cases hstab : τ ∈ stabSub ((commSub ⊤ L).map g.toMonoidHom)
  · exact s16h_e3_l3_central_conj_comm_rank_stab hW ht ht2 ht1 htr hconc hcomp hthin hZ hL3
      hd2 hτ hτ2 hτ1 hτN hτC hg hgN hstab hne
  · exact s16h_e3_l3_central_conj_comm_rank_move hW ht ht2 ht1 htr hconc hcomp hthin hZ hL3
      hd2 hτ hτ2 hτ1 hτN hτC hg hgN hstab hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

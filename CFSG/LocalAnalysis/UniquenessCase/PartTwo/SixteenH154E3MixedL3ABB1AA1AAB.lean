module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB1AA1AABA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB1AA1AABB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_two_centralizer_rank_le
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) = 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∉ centSub (commSub ⊤ L)) :
    rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) ≤
      rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV L) + 2 := by
  have hstab : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ commSub (⊤ : Subgroup W) L,
      x w ∈ commSub (⊤ : Subgroup W) L := by
    intro x hx w hw
    have hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.zpowers_le.mpr hτN hx
    have hxS : x ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
      StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := x)
        (mem_stabSub.2 fun u => by simp) hxN
    exact (mem_stabSub.mp hxS w).mpr hw
  have hdecomp := rk_commSub_add_rk_inf_fixV hstab
  have hcomm := s16h_e3_l3_two_commSub_rank_ge_four hW ht ht2 ht1 htr hconc hcomp hthin hZ
    hL3 hd2 hτ hτ2 hτ1 hτN hτC
  have heq := s16h_e3_l3_two_sum_rank_eq L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) hL3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

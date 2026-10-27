module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BA2AAA1AAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_three_fix_rank_le_eight_aux
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd3 : rk ↥(commSub ⊤ L ⊓ fixV L) = 3)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∉ centSub (commSub ⊤ L)) :
    rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) ≤ 8 := by
  have hup : rk ↥(commSub (⊤ : Subgroup W) L) ≤
      rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV L) + 9 :=
    s16h_e3_l3_three_sum_rank_le L (commSub (⊤ : Subgroup W) L)
      (commSub (⊤ : Subgroup W) L ⊓ fixV L) hL3
  have h4 : 4 ≤ rk ↥(commSub (commSub (⊤ : Subgroup W) L) (Subgroup.zpowers τ)) :=
    s16h_e3_l3_three_commSub_rank_ge_four hW ht ht2 ht1 htr hconc hcomp hthin hZ hL3 hd3
      hτ hτ2 hτ1 hτN hτC
  have hτstab : τ ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
    StabLat.mem_stabSub_commSub (Y := (⊤ : Subgroup W)) (X := L)
      (mem_stabSub.mpr (fun _ => by simp)) hτN
  have hstab : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ commSub (⊤ : Subgroup W) L,
      x w ∈ commSub (⊤ : Subgroup W) L := by
    intro x hx w hw
    have hxstab : x ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
      Subgroup.zpowers_le.mpr hτstab hx
    exact (mem_stabSub.mp hxstab w).mpr hw
  have hident := rk_commSub_add_rk_inf_fixV (V := W) (g := τ)
    (W := commSub (⊤ : Subgroup W) L) hstab
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

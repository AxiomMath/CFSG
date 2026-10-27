module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAAAA
public import CFSG.Quasithin.Background.F918Z8Sz7Qa

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_e3_l3_three_ne_bot_dim_le_two_fix_rank [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL3 : s16h_H5L3Sum L (commSub (⊤ : Subgroup W) L)
      (commSub (⊤ : Subgroup W) L ⊓ fixV L) 3)
    {τ : MulAut W} (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hτC : τ ∉ centSub (commSub (⊤ : Subgroup W) L)) :
    rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) ≤
      rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV L) + 6 := by
  have hτstab : τ ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
    StabLat.mem_stabSub_commSub (X := L) (Y := (⊤ : Subgroup W))
      (mem_stabSub.mpr (fun _ => by simp)) hτN
  have hAstab : Subgroup.zpowers τ ≤ stabSub (commSub (⊤ : Subgroup W) L) :=
    Subgroup.zpowers_le.mpr hτstab
  have hle := rk_inf_fixV_le_autSec_gen (A := Subgroup.zpowers τ)
    (W := commSub (⊤ : Subgroup W) L) (U := commSub (⊤ : Subgroup W) L ⊓ fixV L)
    inf_le_left hAstab
  have hcore := s16h_e3_l3_three_fix_rank_section hW hL3 hτ2 hτ1 hτN hτC
  have hZU : rk ↥((commSub (⊤ : Subgroup W) L ⊓ fixV L) ⊓ fixV (Subgroup.zpowers τ)) ≤
      rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV L) := rk_mono inf_le_left
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

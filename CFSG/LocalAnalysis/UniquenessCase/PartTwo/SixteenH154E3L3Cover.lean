module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoverA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoverB
public import CFSG.Quasithin.Background.B5NonA
public import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_l3_cover_rank_two (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) = 2)
    {τ : MulAut W} (hτ2 : τ ^ 2 = 1) (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hτC : τ ∉ centSub (commSub ⊤ L)) :
    rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) ≤
      rk ↥(commSub ⊤ L ⊓ fixV L) + 2 := by
  have hstab : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ commSub (⊤ : Subgroup W) L,
      x w ∈ commSub (⊤ : Subgroup W) L := by
    intro x hx w hw
    have hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.zpowers_le.mpr hτN hx
    have hxS : x ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
      StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := x)
        (mem_stabSub.2 fun u => by simp) hxN
    exact (mem_stabSub.mp hxS w).mpr hw
  have hdecomp := rk_commSub_add_rk_inf_fixV (V := W) (g := τ)
    (W := commSub (⊤ : Subgroup W) L) hstab
  have hcomm := s16h_e3_l3_cover_commSub_four hW hL3 hd2 (Or.inl rfl) hτ2 hτN hτC
  have hUrank := s16h_e3_l3_sum_rank_four L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 hL3 hd2
  omega

theorem s16h_l3_cover_rank_three (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd3 : rk ↥(commSub ⊤ L ⊓ fixV L) = 3)
    {τ : MulAut W} (hτ2 : τ ^ 2 = 1) (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hτC : τ ∉ centSub (commSub ⊤ L)) :
    rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) ≤
      rk ↥(commSub ⊤ L ⊓ fixV L) + 5 := by
  have hstab : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ commSub (⊤ : Subgroup W) L,
      x w ∈ commSub (⊤ : Subgroup W) L := by
    intro x hx w hw
    have hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.zpowers_le.mpr hτN hx
    have hxS : x ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
      StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := x)
        (mem_stabSub.2 fun u => by simp) hxN
    exact (mem_stabSub.mp hxS w).mpr hw
  have hdecomp := rk_commSub_add_rk_inf_fixV (V := W) (g := τ)
    (W := commSub (⊤ : Subgroup W) L) hstab
  have hcomm := s16h_e3_l3_cover_commSub_four hW hL3 hd3 (Or.inr rfl) hτ2 hτN hτC
  have hUrank := s16h_e3_l3_sum_rank_four L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 hL3 hd3
  omega

theorem s16h_l3_cover_section_six (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {τ : MulAut W} (hτ2 : τ ^ 2 = 1) (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hτC : τ ∉ centSub (commSub ⊤ L)) :
    rk (fixV (autSec (Subgroup.zpowers τ) (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))) ≤ 6 := by
  have hτstab : τ ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
    StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := τ)
      (mem_stabSub.2 fun u => by simp) hτN
  have hτW : Subgroup.zpowers τ ≤ stabSub (commSub (⊤ : Subgroup W) L) :=
    Subgroup.zpowers_le.mpr hτstab
  have hτF : τ ∈ stabSub (fixV L) := by
    rw [mem_stabSub]
    intro z
    constructor
    · intro hz
      have hmem : τ⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hτN
      have h1 := fixV_apply_mem_of_mem_normalizer (L := L) hmem hz
      simpa using h1
    · intro hz
      exact fixV_apply_mem_of_mem_normalizer (L := L) hτN hz
  have hτZ : Subgroup.zpowers τ ≤
      stabSub (commSub (⊤ : Subgroup W) L ⊓ fixV L) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [mem_stabSub]
    intro z
    constructor
    · intro hz
      exact ⟨(mem_stabSub.mp hτstab z).mp hz.1, (mem_stabSub.mp hτF z).mp hz.2⟩
    · intro hz
      exact ⟨(mem_stabSub.mp hτstab z).mpr hz.1, (mem_stabSub.mp hτF z).mpr hz.2⟩
  have hbridge := s16h_rk_fixV_autSec_commSub_zpowers (V := W) (τ := τ)
    (W := commSub (⊤ : Subgroup W) L) (U := commSub (⊤ : Subgroup W) L ⊓ fixV L) hτW hτZ
  rw [rk_top] at hbridge
  have hcomm := s16h_e3_l3_cover_section_commSub_three hW hL3 hτ2 hτN hτC
  have hUrank := s16h_e3_l3_sum_rank L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 hL3
  have hsec := B5.rk_sec_add (W := commSub (⊤ : Subgroup W) L)
    (U := commSub (⊤ : Subgroup W) L ⊓ fixV L) inf_le_left
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

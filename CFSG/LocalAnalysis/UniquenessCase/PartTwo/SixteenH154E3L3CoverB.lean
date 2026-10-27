module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Bridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3InnerB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3OuterB
import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_cover_commSub_four (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {k : ℕ}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k)
    (hd : rk ↥(commSub ⊤ L ⊓ fixV L) = k) (hk : k = 2 ∨ k = 3)
    {τ : MulAut W} (hτ2 : τ ^ 2 = 1) (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hτC : τ ∉ centSub (commSub ⊤ L)) :
    4 ≤ rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers τ)) := by
  obtain ⟨S⟩ := s16h_e3_l3_split_nonempty hW hL3 hd
  by_cases hinn : ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹
  · obtain ⟨γ, hγL, hγ⟩ := hinn
    exact s16h_e3_l3_rank_inner hW S (by omega) hτ2 hτC hγL hγ
  · exact s16h_e3_l3_rank_outer hW S (by omega) hτN hinn

theorem s16h_e3_l3_cover_section_commSub_three (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {τ : MulAut W} (hτ2 : τ ^ 2 = 1) (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hτC : τ ∉ centSub (commSub ⊤ L)) :
    3 ≤ rk ↥(commSub (⊤ : Subgroup (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)))
        (autSec (Subgroup.zpowers τ) (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))) := by
  have hτstab : τ ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
    StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := τ)
      (mem_stabSub.2 fun u => by simp) hτN
  have hτF : τ ∈ stabSub (fixV L) := by
    rw [mem_stabSub]
    intro z
    constructor
    · intro hz
      have hmem : τ⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hτN
      simpa using fixV_apply_mem_of_mem_normalizer (L := L) hmem hz
    · exact fun hz => fixV_apply_mem_of_mem_normalizer (L := L) hτN hz
  have hτZ : Subgroup.zpowers τ ≤ stabSub (commSub (⊤ : Subgroup W) L ⊓ fixV L) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [mem_stabSub]
    intro z
    exact ⟨fun hz => ⟨(mem_stabSub.mp hτstab z).mp hz.1, (mem_stabSub.mp hτF z).mp hz.2⟩,
      fun hz => ⟨(mem_stabSub.mp hτstab z).mpr hz.1, (mem_stabSub.mp hτF z).mpr hz.2⟩⟩
  have hbr := s16h_e3_l3_rk_commSub_autSec_add (τ := τ) (U := commSub ⊤ L)
    (Z := commSub ⊤ L ⊓ fixV L) inf_le_left (Subgroup.zpowers_le.mpr hτstab) hτZ
  by_cases hinn : ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹
  · obtain ⟨γ, hγL, hγ⟩ := hinn
    have := s16h_e3_l3_section_inner hW hL3 hτ2 hτC hγL hγ
    omega
  · have := s16h_e3_l3_section_outer (by norm_num) hL3 hτN hinn
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

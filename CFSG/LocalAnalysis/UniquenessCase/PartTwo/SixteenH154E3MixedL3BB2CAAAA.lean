module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.Quasithin.Background.B5Bot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_e3_l3_three_fix_rank_section [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL3 : s16h_H5L3Sum L (commSub (⊤ : Subgroup W) L)
      (commSub (⊤ : Subgroup W) L ⊓ fixV L) 3)
    {τ : MulAut W} (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hτC : τ ∉ centSub (commSub (⊤ : Subgroup W) L)) :
    rk (fixV (autSec (Subgroup.zpowers τ) (commSub (⊤ : Subgroup W) L)
      (commSub (⊤ : Subgroup W) L ⊓ fixV L))) ≤ 6 := by
  by_cases hZ : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥
  · rw [hZ]
    obtain ⟨hSLn, hsum⟩ := hL3
    rw [hZ] at hsum
    have hPSL : IsPSL 3 2 1 ↥L :=
      s16c167_isPSL_of_isL3 (s16k_isLn_of_isSLn (n := 3) (by norm_num) hSLn)
    have hNat : NatSum3 L (commSub (⊤ : Subgroup W) L) := s16c167_natSum3_of_sumOfNat hsum
    have ht : τ * τ = 1 := by simpa [pow_two] using hτ2
    have hn : L.map (MulAut.conj τ).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hτN
    have hstab : τ ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
      StabLat.mem_stabSub_commSub (X := L) (Y := (⊤ : Subgroup W))
        (mem_stabSub.mpr (fun _ => by simp)) hτN
    have hJt : (commSub (⊤ : Subgroup W) L).map τ.toMonoidHom =
        commSub (⊤ : Subgroup W) L := by
      apply le_antisymm
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        exact (mem_stabSub.mp hstab y).mpr hy
      · intro x hx
        refine Subgroup.mem_map.mpr ⟨τ⁻¹ x, ?_, by simp⟩
        exact (mem_stabSub.mp ((stabSub (commSub (⊤ : Subgroup W) L)).inv_mem hstab) x).mpr hx
    rcases s16c167_natSum3_involution hW hPSL hNat ht hn hJt with hfix | hquot
    · exfalso
      apply hτC
      rw [mem_centSub]
      intro w hw
      exact (mem_fixV.mp (hfix hw)) τ (Subgroup.mem_zpowers τ)
    · have hcard := B5.card_fixV_autSec_bot (A := Subgroup.zpowers τ)
          (W := commSub (⊤ : Subgroup W) L) (Subgroup.zpowers_le.mpr hstab)
      have hrkfix : rk (fixV (autSec (Subgroup.zpowers τ) (commSub (⊤ : Subgroup W) L) ⊥)) =
          rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) := by
        unfold rk
        rw [hcard]
      have hsumrk : rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) +
          E3.mQuot (commSub (⊤ : Subgroup W) L)
            (commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) =
          rk ↥(commSub (⊤ : Subgroup W) L) := by
        rw [E3.mQuot_eq_rkIdx]
        have h := rk_add_rkIdx ((commSub (⊤ : Subgroup W) L ⊓
          fixV (Subgroup.zpowers τ)).subgroupOf (commSub (⊤ : Subgroup W) L))
        have hc : rk ↥((commSub (⊤ : Subgroup W) L ⊓
            fixV (Subgroup.zpowers τ)).subgroupOf (commSub (⊤ : Subgroup W) L)) =
            rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) := by
          unfold rk
          exact congrArg (padicValNat 2) (Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (inf_le_left :
              (commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) ≤
                commSub (⊤ : Subgroup W) L)).toEquiv)
        rw [hc] at h
        exact h
      have hrkW : rk ↥(commSub (⊤ : Subgroup W) L) = 9 := s16c167_rk_natSum3 hNat
      rw [hrkfix]
      omega
  · exact s16h_l3_cover_section_six hW hL3 hτ2 hτN hτC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

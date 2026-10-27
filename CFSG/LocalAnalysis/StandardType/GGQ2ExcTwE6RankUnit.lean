module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
import CFSG.LocalAnalysis.StandardType.GGQTwoVACUnitDvd
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem card_range_ggGamma_bstar_mul_three (hcfg : GGConfig 3 B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggGamma L hN).range * 3 = Nat.card Bs := by
  have h := NbrU63.card_range_ggGamma_mul_card_inf (K := L) hN
  rw [hcfg.bstar_inf_centralizer_L, Nat.card_zpowers, hcfg.orderOf_x] at h
  exact h

theorem ggLabelIso_not_twA_two_three {lab : LargeEvenLabel} (hn : lab.n < 2)
    (h : GGLabelIso lab ⟨.twA, 2, 3⟩) : False := by
  unfold GGLabelIso at h
  rcases h with h | ⟨-, h, -, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · rw [h] at hn
    exact absurd hn (by decide)
  · rcases h with h | h <;> exact absurd h (by decide)
  · exact absurd (show LargeEvenLieTag.twA = LargeEvenLieTag.A from
      congrArg LargeEvenLabel.tag h) (by decide)
  · exact absurd (show LargeEvenLieTag.twA = LargeEvenLieTag.D from
      congrArg LargeEvenLabel.tag h) (by decide)
  · exact absurd (show (2 : ℕ) = 3 from congrArg LargeEvenLabel.rank h) (by decide)
  · exact absurd (show LargeEvenLieTag.twA = LargeEvenLieTag.twD from
      congrArg LargeEvenLabel.tag h) (by decide)
  · exact absurd (show LargeEvenLieTag.twA = LargeEvenLieTag.A from
      congrArg LargeEvenLabel.tag h) (by decide)
  · exact absurd (show LargeEvenLieTag.twA = LargeEvenLieTag.twD from
      congrArg LargeEvenLabel.tag h) (by decide)

theorem excTwE6_rank_of_unit
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (hT : lab = ⟨.twA, 5, 1⟩ ∨ lab = ⟨.twA, 4, 1⟩ ∨ lab = ⟨.twA, 2, 3⟩) :
    3 ^ 5 ≤ Nat.card Bs := by
  obtain ⟨-, lab₀, hlab₀, hraw₀⟩ := hS.2.1
  obtain ⟨R₀, hR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw₀
  obtain ⟨hsimple₀, hnab₀, θ₀, hprop₀⟩ := hQ₀
  obtain ⟨hq₀, hBsN, hBsI0₀⟩ := hprop₀
  have hhas₀ : GGHasLabel lab₀ (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw₀
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hcard := card_range_ggGamma_bstar_mul_three hS.1.1 hBsN
  have hID : GGInnerDiagOn Bs L := largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hS.2.1
  have hmark := ggInnerDiagOn_relabel ggLabelRigidInput_holds hID hΛ hhas
  obtain ⟨hperf, lab', hlab', hraw⟩ := hmark
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hsimple, hnab, θ, hprop⟩ := hQ
  obtain ⟨hlab'eq, hBsN', hBsI0⟩ := hprop
  rcases hT with rfl | rfl | rfl
  ·
    rw [hlab'eq] at hraw
    obtain ⟨K, hfield, hfin, hK, hQ₂⟩ := hraw
    let _ : Field K := hfield
    let _ : Finite K := hfin
    obtain ⟨hsimple₂, hnab₂, θ₂, hprop₂⟩ := hQ₂
    obtain ⟨-, -, hBsI0₂⟩ := hprop₂
    have hγ := ggQ2UnitDvd_gamma_ge_at (lab := ⟨.twA, 5, 1⟩) (K := K) (θ := θ₂) hS hΛ
      (show (1 : ℕ) < 2 from by norm_num) rfl (show 3 ∣ 6 from by norm_num) hK hsimple₂ hnab₂
      hBsN hBsI0₂ hperf
    have hγ4 : 3 ^ 4 ≤ Nat.card (ggGamma L hBsN).range := by
      have h4 : (5 + 1) / 3 + 2 = 4 := by norm_num
      rwa [h4] at hγ
    rw [← hcard]
    calc 3 ^ 5 = 3 ^ 4 * 3 := by norm_num
      _ ≤ Nat.card (ggGamma L hBsN).range * 3 := Nat.mul_le_mul_right 3 hγ4
  ·
    rw [hlab'eq] at hraw
    obtain ⟨K, hfield, hfin, hK, hQ₂⟩ := hraw
    let _ : Field K := hfield
    let _ : Finite K := hfin
    obtain ⟨hsimple₂, hnab₂, θ₂, hprop₂⟩ := hQ₂
    obtain ⟨-, -, hBsI0₂⟩ := hprop₂
    have hγ : Nat.card (ggGamma L hBsN).range = 3 ^ 4 := by
      have h := ggQ2Unit_gamma_card (K := K) (n := 1) (d := 5) (θ := θ₂) hS hK
        (show 1 ≤ 1 from by norm_num) (show 3 ≤ 5 from by norm_num)
        (show 3 ∣ 3 from by norm_num) (show ¬ 3 ∣ 5 from by norm_num) hperf hBsN hBsI0₂
      have h4 : 5 - 1 = 4 := by norm_num
      rwa [h4] at h
    rw [← hcard, hγ]
    norm_num
  ·
    exact absurd (ggLabelRigidInput_holds lab₀ ⟨.twA, 2, 3⟩ (↥L ⧸ Subgroup.center ↥L) hlab₀
      hΛ hhas₀ hhas) (ggLabelIso_not_twA_two_three hq₀)

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end

module

public import CFSG.Quasithin.Vol2.Ch10SecI1DualH
public import CFSG.Quasithin.Vol2.Ch10SecI1CovG2
public import CFSG.Quasithin.Vol2.Ch10SecI1CovO4
public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.H13.VolIAltCoverEight
public import CFSG.Quasithin.H13.VolII16SL3
public import CFSG.Quasithin.H13.VolII16Wedge
public import CFSG.Quasithin.H13.VolII16A7Four
public import CFSG.Quasithin.H13.VolII16Scalar

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank Subgroup
open CFSG.Open (quasithinG2)


theorem as_I_1_6_cover_holds : AS_I_1_6_cover := by
  intro W _ _ hW2 Gm d hcomm hmod
  obtain ⟨-, -, -, -, -, t2, tO, -, -, tSp, tG2, -, -, -, -, -, -⟩ :=
    SteinbergCB.I16.natural_binary_module_first_cohomology.{0, 0}
  have hbot : fixV Gm = ⊥ → Nat.card (fixV Gm) ≤ 2 ^ d := fun h => by
    rw [h, card_bot]
    exact Nat.one_le_two_pow
  have htwo : Nat.card (fixV Gm) ≤ 2 → d = 1 → Nat.card (fixV Gm) ≤ 2 ^ d := fun h hd => by
    rw [hd, pow_one]
    exact h
  rcases hmod with ⟨m, hm, hd, hR⟩ | ⟨m, hm, hd, hR⟩ | ⟨a, ha, hd, K, _, _, hK, hR⟩ |
    ⟨a, ha, hd, K, _, _, _, hK, hR⟩ | ⟨a, ha, hd, K, _, _, hK, hR⟩ | ⟨hd, K, _, _, hK, hR⟩ |
    ⟨a, ha, hd, K, _, _, hK, hR⟩ | ⟨a, ha, hd, K, _, _, hK, hR⟩ | ⟨m, hm, hd, K, _, _, hK, hR⟩ |
    ⟨hd, hR⟩ | ⟨hd, α, hR⟩ | ⟨hd, K, _, _, Γ₀, -, -, hhat, hsc, hR⟩
  ·
    rcases hm with rfl | rfl
    · exact hbot (H13.VolI.altNaturalCoverFive_holds W hW2 Gm _ le_rfl hcomm hR)
    · exact hbot (H13.VolI.altNaturalCoverSeven_holds W hW2 Gm _ le_rfl hcomm hR)
  ·
    rcases hm with rfl | rfl
    · rcases H13.VolI.altNaturalCoverSix_holds W hW2 Gm _ le_rfl hcomm hR with h | ⟨h, -⟩
      · exact hbot h
      · exact htwo h.le hd
    · rcases H13.VolI.altNaturalCoverEight_holds W hW2 Gm _ le_rfl hcomm hR with h | ⟨h, -⟩
      · exact hbot h
      · exact htwo h.le hd
  ·
    have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    let _ := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 ^ a := by rw [Fintype.card_eq_nat_card]; exact hK
    exact C10KH.sl2Cover_card_le hW2 le_rfl hcomm hR fun ρ hρ => by
      have := t2 hK' ha hρ
      omega
  ·
    let _ := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 ^ (2 * a) := by rw [Fintype.card_eq_nat_card]; exact hK
    exact C10KH.orth4Cover_card_le ha hK hW2 le_rfl hcomm hR fun ρ hρ => by
      have := tO hK' (by omega) hρ
      omega
  ·
    exact hbot (H13.VolI.sl3_cover ha hK hW2 le_rfl hcomm hR)
  ·
    exact htwo (H13.VolI.natSL_card_le card_Z1A_three (by simpa using hK) hW2 le_rfl hcomm hR) hd
  ·
    have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    let _ := Fintype.ofFinite K
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have hK' : Fintype.card K = 2 ^ a := by rw [Fintype.card_eq_nat_card]; exact hK
    exact C10KH.sp4Cover_card_le hW2 le_rfl hcomm hR fun ρ hρ => by
      have := tSp hK' (by omega) (C10KH.sp4Derived_of_isModel hK4 hρ)
      omega
  ·
    have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    let _ := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 ^ a := by rw [Fintype.card_eq_nat_card]; exact hK
    exact C10KH.g2Cover_card_le hW2 le_rfl hcomm hR fun ρ hρ => by
      have := tG2 hK' (by omega) (C10KH.g2Derived_of_isModel hρ)
      omega
  ·
    rcases hm with rfl | rfl
    · exact hbot (H13.VolI.natSL_eq_bot Z1A_eq_B1A_four (by simpa using hK) hW2 le_rfl hcomm hR)
    · exact hbot (H13.VolI.natSL_eq_bot Z1A_eq_B1A_five (by simpa using hK) hW2 le_rfl hcomm hR)
  ·
    exact hbot (H13.VolI.wedge_cover hW2 le_rfl hcomm hR)
  ·
    exact hbot (H13.VolI.a7Four_cover hW2 le_rfl hcomm hR)
  ·
    have hc3 : Nat.card (center ↥Γ₀) = 3 := hhat.2.1
    have hne : center ↥Γ₀ ≠ ⊥ := fun h0 => by
      rw [h0, card_bot] at hc3
      omega
    obtain ⟨⟨g₀, hg₀c⟩, hg₀1⟩ := (ne_bot_iff_exists_ne_one).1 hne
    have hg₀3 : g₀ ^ 3 = 1 := by
      have h1 : (⟨g₀, hg₀c⟩ : ↥(center ↥Γ₀)) ^ Nat.card ↥(center ↥Γ₀) = 1 := pow_card_eq_one'
      rw [hc3] at h1
      exact congrArg Subtype.val h1
    obtain ⟨c, hc⟩ := hsc g₀ hg₀c
    have hc1 : c ≠ 1 := by
      rintro rfl
      apply hg₀1
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      rw [hc, one_smul]
      rfl
    exact hbot (H13.VolI.nat_eq_bot_of_central_scalar (fun g => (mem_center_iff.1 hg₀c g)) hc1 hc
      ⟨1, rfl⟩ hg₀3 hW2 le_rfl hcomm hR)

theorem lemI1_6_holds : AS_I_1_6 :=
  lemI1_6_of as_I_1_6_cover_holds as_I_1_6_dual_holds

end CFSG.Quasithin.ASInputs

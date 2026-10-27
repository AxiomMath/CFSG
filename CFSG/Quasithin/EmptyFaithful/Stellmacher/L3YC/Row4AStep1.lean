module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCLemmaUBar
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCClassIIRows

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Stellmacher.L3YC

variable {G : Type} [Group G] [Finite G]

theorem card_pCore_le_eight_of_le_L42 {Y : Type} [Group Y] [Finite Y] {B N : Subgroup Y}
    (hBN : B ≤ N) (h3 : IsPSL 3 2 1 (ModO2 B)) (h4 : IsPSL 4 2 1 ↥N) :
    Nat.card (CFSG.pCore 2 ↥B) ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Nat.card ↥N = 20160 := by
    rw [CD.L3YC.L32.card_of_isPSL (by norm_num) h4]
    decide
  have hd : Nat.card ↥B ∣ 20160 := hN ▸ Subgroup.card_dvd_of_le hBN
  have h2 : Nat.card ↥B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) := by
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
  rw [PU.L3YC.card_L32 h3] at h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥B) (p := 2))
  rw [hk] at h2 ⊢
  by_contra hlt
  have hk4 : 4 ≤ k := by
    by_contra h
    have : k ≤ 3 := by omega
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h16 : 2 ^ 4 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk4
  have : 168 * 2 ^ 4 ∣ 20160 := by
    rw [h2] at hd
    exact (Nat.mul_dvd_mul_left 168 h16).trans hd
  omega

theorem row4a_cq_le_pCore
    {H G₀ R L L₁ : Subgroup G} (hLH : L ≤ H) (hLL₁ : L ≤ L₁)
    (hLG : L ≤ G₀) (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3)
    (hperf : ⁅L, L⁆ = L) (h : MS93.IsC134Case4Corr G₀ R L)
    (h42 : IsPSL 4 2 1 ↥(modO2Image H L₁)) :
    (Nat.card ↥(PU.L3YC.Qbar H G₀ L) = 8 ∨ PU.L3YC.Qbar H G₀ L = ⊥) ∧
    ∀ v ∈ c134CQ G₀ L, ∀ hv : v ∈ H, (⟨v, hv⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := by
  have hQL : c134Q G₀ L ≤ L := (MS93.commutator_le_pCoreOf hLG hGL).trans (pCoreOf_le 2 L)
  have hLL : modO2Image H L ≤ modO2Image H L₁ := Subgroup.map_mono fun _ hx => hLL₁ hx
  have h3 : IsPSL 3 2 1 (ModO2 (modO2Image H L)) := CD.L3YC.isPSL_modO2_modO2Image hLH hq
  have hp8 := card_pCore_le_eight_of_le_L42 hLL h3 h42
  obtain ⟨-, hK1⟩ := PU.L3YC.card_pCore_modO2Image_le (H := H) hLH hLG hGL hq hperf h
  have hQ8 : Nat.card ↥(PU.L3YC.Qbar H G₀ L) ≤ 8 := by
    refine (Subgroup.card_le_of_le hK1).trans ?_
    rw [Subgroup.card_map_of_injective (modO2Image H L).subtype_injective]
    exact hp8
  obtain ⟨hCc, -, -⟩ := PU.L3YC.lemmaU_bar_U1 (H := H) hLH hLG hGL hq h
  have hCQ : PU.L3YC.Cbar H G₀ L ≤ PU.L3YC.Qbar H G₀ L :=
    Subgroup.map_mono fun x hx => (Subgroup.mem_inf.mp hx).1
  have hcomm : PU.L3YC.Qbar H G₀ L = ⁅PU.L3YC.Qbar H G₀ L, modO2Image H L⁆ := by
    have hQH : c134Q G₀ L ≤ H := hQL.trans hLH
    have hself := CD.L3YC.comm_self_of_case4Corr h
    have h1 : ⁅(c134Q G₀ L).subgroupOf H, L.subgroupOf H⁆ = (c134Q G₀ L).subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hQH, inf_eq_left.mpr hLH, hself]
    unfold PU.L3YC.Qbar modO2Image
    rw [← Subgroup.map_commutator, h1]
  have hU2 := PU.L3YC.lemmaU_bar_U2 (H := H) hLH hLG hGL hq h
      (D' := PU.L3YC.Cbar H G₀ L)
      (fun b hb y hy => by
        have := Subgroup.mem_centralizer_iff.mp (hCc hy) b hb
        rw [show b * y * b⁻¹ = y by rw [this, mul_assoc, mul_inv_cancel, mul_one]]; exact hy) le_rfl hCQ
  have hCbot : PU.L3YC.Cbar H G₀ L = ⊥ := by
    obtain ⟨j, hj⟩ := hU2
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have hQC : PU.L3YC.Cbar H G₀ L = PU.L3YC.Qbar H G₀ L := by
        refine Subgroup.eq_of_le_of_card_ge hCQ ?_
        simp at hj
        exact hj.le
      have hcen : PU.L3YC.Qbar H G₀ L ≤ Subgroup.centralizer (modO2Image H L : Set _) :=
        hQC ▸ hCc
      have hbot : ⁅PU.L3YC.Qbar H G₀ L, modO2Image H L⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcen
      rw [← hcomm] at hbot
      exact le_bot_iff.mp (hQC ▸ hbot.le)
    · have h8 : 8 ≤ 8 ^ j := by
        calc 8 = 8 ^ 1 := by norm_num
          _ ≤ 8 ^ j := Nat.pow_le_pow_right (by norm_num) hj0
      have hpos : 0 < Nat.card ↥(PU.L3YC.Cbar H G₀ L) := Nat.card_pos
      have : Nat.card ↥(PU.L3YC.Cbar H G₀ L) = 1 := by
        have : Nat.card ↥(PU.L3YC.Cbar H G₀ L) * 8 ≤ 8 := by
          calc _ ≤ Nat.card ↥(PU.L3YC.Cbar H G₀ L) * 8 ^ j := Nat.mul_le_mul_left _ h8
            _ = _ := hj.symm
            _ ≤ 8 := hQ8
        omega
      exact Subgroup.card_eq_one.mp this
  refine ⟨?_, ?_⟩
  · obtain ⟨j, hj⟩ := hU2
    rw [hCbot, Subgroup.card_bot, one_mul] at hj
    have hj1 : j ≤ 1 := by
      by_contra hc
      have : 8 ^ 2 ≤ 8 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases j
    · right
      exact Subgroup.card_eq_one.mp (by simpa using hj)
    · left
      simpa using hj
  · intro v hv hvH
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨v, hvH⟩ ∈ PU.L3YC.Cbar H G₀ L :=
      ⟨⟨v, hvH⟩, hv, rfl⟩
    rw [hCbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmem

end Stellmacher.L3YC

end CFSG.Quasithin

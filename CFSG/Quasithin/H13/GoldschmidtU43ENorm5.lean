module

public import CFSG.Quasithin.H13.GoldschmidtU43ENorm4
public import CFSG.Adapters.Involutions
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm1

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

abbrev Nbar : Type := ↥S.Ng ⧸ S.Mg.subgroupOf S.Ng

theorem u43_odd_card_oddCore {K : Type} [Group K] [Finite K] : Odd (Nat.card (CFSG.oddCore K)) := by
  rw [CFSG.BrauerSuzuki.Helpers.odd_natCard_iff_no_involution]
  intro x hx
  have := CFSG.Adapters.odd_orderOf_of_mem_oddCore x.2
  rw [Subgroup.orderOf_coe, hx] at this
  exact absurd this (by decide)

theorem Mg_le_oddCore_Ng : S.Mg.subgroupOf S.Ng ≤ CFSG.oddCore ↥S.Ng := by
  have hodd : Odd (Nat.card (S.Mg.subgroupOf S.Ng)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.Mg_le_Ng).toEquiv]
    exact S.odd_card_Mg
  exact CFSG.BrauerSuzuki.Helpers.normal_odd_le_oddCore _ inferInstance hodd

theorem oddCore_Ng : CFSG.oddCore ↥S.Ng = S.Mg.subgroupOf S.Ng := by
  have hle := S.Mg_le_oddCore_Ng
  set Y : Subgroup ↥S.Ng := CFSG.oddCore ↥S.Ng with hY
  set Yg : Subgroup G := Y.map S.Ng.subtype with hYg
  have hcard : Nat.card Yg = Nat.card Y :=
    Subgroup.card_map_of_injective S.Ng.subtype_injective
  have hYodd : Odd (Nat.card Y) := u43_odd_card_oddCore
  have hconj : ∀ g : G, g ∈ S.Ng → ∀ x ∈ Yg, g * x * g⁻¹ ∈ Yg := by
    rintro g hg _ ⟨y, hy, rfl⟩
    refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : Y.Normal).conj_mem y hy ⟨g, hg⟩
  have hnorm : ∀ g : G, g ∈ S.Ng → g ∈ Subgroup.normalizer (Yg : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj g hg x, fun hx => ?_⟩
    have := hconj g⁻¹ (S.Ng.inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this
  have hσ : S.sig ∈ Yg := by
    have hσM : S.sig ∈ S.Mg := S.Tg_le_Mg S.sig_mem_Tg
    exact ⟨⟨S.sig, S.Mg_le_Ng hσM⟩, hle hσM, rfl⟩
  have h81 : Nat.card Yg ≤ 81 :=
    S.card_le_81_of_odd (hcard ▸ hYodd) (hnorm z S.z_mem_Ng) (hnorm _ S.u_mem_Ng) hσ
  have hM : Nat.card (S.Mg.subgroupOf S.Ng) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.Mg_le_Ng).toEquiv]
    exact S.card_Mg_eq_81
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hM, ← hcard]; exact h81)).symm

theorem oddCore_Nbar : CFSG.oddCore S.Nbar = ⊥ := by
  set MK : Subgroup ↥S.Ng := S.Mg.subgroupOf S.Ng with hMK
  set π : ↥S.Ng →* S.Nbar := QuotientGroup.mk' MK with hπ
  set Y' : Subgroup ↥S.Ng := (CFSG.oddCore S.Nbar).comap π with hY'
  have hnorm : Y'.Normal := (inferInstance : (CFSG.oddCore S.Nbar).Normal).comap π
  have hodd : Odd (Nat.card Y') := by
    rw [CFSG.BrauerSuzuki.Helpers.odd_natCard_iff_no_involution]
    intro x hx2
    have hx : (x : ↥S.Ng) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at hx2
      exact hx2 ▸ pow_orderOf_eq_one _
    have hπx : π x ∈ CFSG.oddCore S.Nbar := x.2
    have hπ2 : (π x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    have hodd1 : Odd (orderOf (π x)) := CFSG.Adapters.odd_orderOf_of_mem_oddCore hπx
    have hdvd : orderOf (π x) ∣ 2 := orderOf_dvd_of_pow_eq_one hπ2
    have h1 : orderOf (π x) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd1
        exact absurd hodd1 (by decide)
    have hπ1 : π x = 1 := orderOf_eq_one_iff.mp h1
    have hxM : (x : ↥S.Ng) ∈ CFSG.oddCore ↥S.Ng := by
      rw [S.oddCore_Ng]
      exact (QuotientGroup.eq_one_iff _).mp hπ1
    have := CFSG.Adapters.odd_orderOf_of_mem_oddCore hxM
    rw [Subgroup.orderOf_coe, hx2] at this
    exact absurd this (by decide)
  have hle : Y' ≤ CFSG.oddCore ↥S.Ng := CFSG.BrauerSuzuki.Helpers.normal_odd_le_oddCore _ hnorm hodd
  rw [S.oddCore_Ng] at hle
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have hk : k ∈ Y' := hy
  exact (QuotientGroup.eq_one_iff k).mpr (hle hk)

end JWSetup

end CFSG.Quasithin.H13.U43

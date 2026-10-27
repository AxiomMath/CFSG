module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocBurn

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G)

@[expose] noncomputable def tG : G := C.Φ2 tPrime

@[expose] noncomputable def QG : Subgroup G := Subgroup.map C.φ2 (QY.subgroupOf P2)

theorem tG_def : C.tG = C.Φ2 tPrime := rfl

theorem mem_QG {g : G} : g ∈ C.QG ↔ ∃ q ∈ QY, C.Φ2 q = g := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, C.Φ2_of_mem x.2⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, QY_le_P2 hq⟩, hq, (C.Φ2_of_mem _).symm⟩

theorem card_QG : Nat.card C.QG = 32 := by
  rw [QG, Subgroup.card_map_of_injective C.inj2,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe QY_le_P2).toEquiv, card_QY]

theorem isPGroup_QG : IsPGroup 2 C.QG := by
  have h : IsPGroup 2 QY := isSylow_T.2.1.to_le (fun _ hg => (mem_QY_iff.1 hg).1)
  have : IsPGroup 2 (QY.subgroupOf P2) :=
    IsPGroup.of_equiv h (Subgroup.subgroupOfEquivOfLe QY_le_P2).symm
  exact this.map _

theorem tG_ne_one : C.tG ≠ 1 := by
  intro h
  have : C.Φ2 tPrime = C.Φ2 1 := by rw [C.Φ2_one]; exact h
  exact tPrime_ne_one (C.Φ2_inj (Vsub_le_P2 tPrime_mem_Vsub) P2.one_mem this)

theorem tG_mem_QG : C.tG ∈ C.QG := C.mem_QG.2 ⟨tPrime, tPrime_mem_QY, rfl⟩

theorem QG_le_centralizer : C.QG ≤ Subgroup.centralizer ({C.tG} : Set G) := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := C.mem_QG.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff, tG_def, ← C.Φ2_mul (QY_le_P2 hq)
    (Vsub_le_P2 tPrime_mem_Vsub), ← C.Φ2_mul (Vsub_le_P2 tPrime_mem_Vsub) (QY_le_P2 hq),
    (mem_QY_iff.1 hq).2]

variable [Finite G]

theorem QG_maximal (Q' : Subgroup G) (hQ'H : Q' ≤ Subgroup.centralizer ({C.tG} : Set G))
    (hQ'p : IsPGroup 2 Q') (hle : C.QG ≤ Q') : Q' = C.QG := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨S, hS⟩ := C.exists_sylow_TG
  have hSc : Nat.card S = 64 := by rw [hS, C.card_TG]
  have hgt : 32 < Nat.card Q' := by
    refine lt_of_le_of_ne (C.card_QG ▸ Subgroup.card_le_of_le hle) fun h => hne ?_
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [C.card_QG, ← h])).symm
  obtain ⟨n, hn⟩ := hQ'p.exists_card_eq
  obtain ⟨S', hS'⟩ := hQ'p.exists_le_sylow
  have hS'c : Nat.card S' = 64 := by
    rw [Sylow.card_eq_multiplicity S', ← Sylow.card_eq_multiplicity S, hSc]
  have hle64 : Nat.card Q' ≤ 64 := hS'c ▸ Subgroup.card_le_of_le hS'
  have hn6 : 6 ≤ n := by
    by_contra h
    have : n ≤ 5 := by omega
    have : 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h64 : Nat.card Q' = 64 := by
    have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
    omega
  have hQS' : Q' = (S' : Subgroup G) := Subgroup.eq_of_le_of_card_ge hS' (by rw [hS'c, h64])
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S S'
  have hxS : (MulAut.conj x • (S : Subgroup G) : Subgroup G) = (S' : Subgroup G) := by
    have h1 := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hx
    simpa only [Sylow.coe_subgroup_smul] using h1
  have htQ' : C.tG ∈ Q' := hle C.tG_mem_QG
  rw [hQS', ← hxS, Subgroup.mem_smul_pointwise_iff_exists] at htQ'
  obtain ⟨s, hsS, hst⟩ := htQ'
  have hsT : s ∈ C.TG := hS ▸ hsS
  have hst' : x * s * x⁻¹ = C.tG := hst
  have hcen : ∀ g ∈ C.TG, g * s = s * g := by
    intro g hg
    have hgS : x * g * x⁻¹ ∈ Q' := by
      rw [hQS', ← hxS, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨g, hS ▸ hg, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hQ'H hgS)
    rw [← hst'] at h1
    have h2 : x * g * x⁻¹ * (x * s * x⁻¹) = x * s * x⁻¹ * (x * g * x⁻¹) := h1
    have h3 : x * (g * s) * x⁻¹ = x * (s * g) * x⁻¹ := by
      calc x * (g * s) * x⁻¹ = x * g * x⁻¹ * (x * s * x⁻¹) := by group
        _ = x * s * x⁻¹ * (x * g * x⁻¹) := h2
        _ = x * (s * g) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h3)
  rcases C.central_TG hsT hcen with h | h
  · apply C.tG_ne_one
    rw [← hst', h]
    group
  · exact C.not_conj_z tPrime_mem_Vsub not_isConj_tPrime x (by rw [← tG_def, ← hst', h])

end Ctx

end CFSG.Quasithin.H13.F431.U42

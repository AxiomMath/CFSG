module

public import CFSG.Quasithin.SteinbergCBIrreducibleTI

public section

namespace CFSG.Quasithin.SteinbergCB

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem commutator_eq_bot_iff_forall_commute {H₁ H₂ : Subgroup G} :
    ⁅H₁, H₂⁆ = ⊥ ↔ ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x := by
  rw [commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro h x hx y hy
    exact (mem_centralizer_iff.1 (h hx) y hy).symm
  · intro h x hx
    exact mem_centralizer_iff.2 fun y hy => (h x hx y hy).symm

theorem linear_weak_closure_normalizing_conjugates_centralize [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {V : Subgroup G} (hVT : V ≤ T) (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hcomm : ∀ g : G, MulAut.conj g⁻¹ • V ≤ T → ⁅V, MulAut.conj g⁻¹ • V⁆ = ⊥)
    (A B : Subgroup G) (hA : ∃ a : G, A = MulAut.conj a⁻¹ • V)
    (hB : ∃ b : G, B = MulAut.conj b⁻¹ • V) (hBA : B ≤ normalizer (A : Set G)) :
    ⁅A, B⁆ = ⊥ := by
  have hVp : IsPGroup p V := T.isPGroup'.to_le hVT
  have key : ∀ c : G, MulAut.conj c⁻¹ • V ≤ normalizer (V : Set G) →
      ∀ v ∈ V, ∀ x ∈ MulAut.conj c⁻¹ • V, v * x = x * v := by
    intro c hc
    set K := normalizer (V : Set G) with hK
    set Bc := MulAut.conj c⁻¹ • V with hBc
    have hBp : IsPGroup p Bc := by
      rw [hBc, pointwise_smul_def]
      exact hVp.map _
    have hBKp : IsPGroup p (Bc.subgroupOf K) :=
      hBp.of_equiv (subgroupOfEquivOfLe hc).symm
    obtain ⟨Q, hQ⟩ := hBKp.exists_le_sylow
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q (T.subtype hTN)
    have hkT : ∀ x ∈ Bc, (k : G) * x * (k : G)⁻¹ ∈ (T : Subgroup G) := by
      intro x hx
      have hxQ : (⟨x, hc hx⟩ : K) ∈ Q := hQ (by simpa [mem_subgroupOf] using hx)
      have h1 : MulAut.conj k • (⟨x, hc hx⟩ : K) ∈ (T.subtype hTN : Subgroup K) := by
        rw [← hk, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ hxQ
      rw [Sylow.coe_subtype, mem_subgroupOf] at h1
      exact h1
    have hle : MulAut.conj (c * (k : G)⁻¹)⁻¹ • V ≤ T := by
      intro y hy
      rw [mem_conj_inv_smul_iff] at hy
      have hyB : (k : G)⁻¹ * y * k ∈ Bc := by
        rw [hBc, mem_conj_inv_smul_iff]
        have : c * ((k : G)⁻¹ * y * k) * c⁻¹ = c * (k : G)⁻¹ * y * (c * (k : G)⁻¹)⁻¹ := by group
        rw [this]
        exact hy
      have := hkT _ hyB
      have heq : (k : G) * ((k : G)⁻¹ * y * k) * (k : G)⁻¹ = y := by group
      rwa [heq] at this
    have h1 := commutator_eq_bot_iff_forall_commute.1 (hcomm _ hle)
    intro v hv x hx
    have hv' : (k : G) * v * (k : G)⁻¹ ∈ V := (mem_normalizer_iff.1 k.2 v).1 hv
    have hx' : (k : G) * x * (k : G)⁻¹ ∈ MulAut.conj (c * (k : G)⁻¹)⁻¹ • V := by
      rw [mem_conj_inv_smul_iff]
      rw [hBc, mem_conj_inv_smul_iff] at hx
      have : c * (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (c * (k : G)⁻¹)⁻¹ = c * x * c⁻¹ := by
        group
      rw [this]
      exact hx
    have h2 := h1 _ hv' _ hx'
    have h3 : (k : G) * (v * x) * (k : G)⁻¹ = (k : G) * (x * v) * (k : G)⁻¹ := by
      calc (k : G) * (v * x) * (k : G)⁻¹ =
            (k : G) * v * (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) := by group
        _ = (k : G) * x * (k : G)⁻¹ * ((k : G) * v * (k : G)⁻¹) := h2
        _ = (k : G) * (x * v) * (k : G)⁻¹ := by group
    simpa using h3
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  have hB' : MulAut.conj (b * a⁻¹)⁻¹ • V ≤ normalizer (V : Set G) := by
    intro x hx
    rw [mem_conj_inv_smul_iff] at hx
    have hy : a⁻¹ * x * a ∈ MulAut.conj b⁻¹ • V := by
      rw [mem_conj_inv_smul_iff]
      have : b * (a⁻¹ * x * a) * b⁻¹ = b * a⁻¹ * x * (b * a⁻¹)⁻¹ := by group
      rw [this]
      exact hx
    have hyN := mem_normalizer_iff.1 (hBA hy)
    rw [mem_normalizer_iff]
    intro v
    have e1 : x * v * x⁻¹ = a * ((a⁻¹ * x * a) * (a⁻¹ * v * a) * (a⁻¹ * x * a)⁻¹) * a⁻¹ := by
      group
    have e2 : ∀ u : G, u ∈ V ↔ a⁻¹ * u * a ∈ MulAut.conj a⁻¹ • V := fun u => by
      rw [mem_conj_inv_smul_iff]
      have : a * (a⁻¹ * u * a) * a⁻¹ = u := by group
      rw [this]
    rw [e2 v, hyN, e1, e2]
    have : a⁻¹ * (a * ((a⁻¹ * x * a) * (a⁻¹ * v * a) * (a⁻¹ * x * a)⁻¹) * a⁻¹) * a =
        (a⁻¹ * x * a) * (a⁻¹ * v * a) * (a⁻¹ * x * a)⁻¹ := by group
    rw [this]
  rw [commutator_eq_bot_iff_forall_commute]
  intro u hu y hy
  have hu' : a * u * a⁻¹ ∈ V := mem_conj_inv_smul_iff.1 hu
  have hy' : a * y * a⁻¹ ∈ MulAut.conj (b * a⁻¹)⁻¹ • V := by
    rw [mem_conj_inv_smul_iff]
    rw [mem_conj_inv_smul_iff] at hy
    have : b * a⁻¹ * (a * y * a⁻¹) * (b * a⁻¹)⁻¹ = b * y * b⁻¹ := by group
    rw [this]
    exact hy
  have h := key _ hB' _ hu' _ hy'
  have h3 : a * (u * y) * a⁻¹ = a * (y * u) * a⁻¹ := by
    calc a * (u * y) * a⁻¹ = a * u * a⁻¹ * (a * y * a⁻¹) := by group
      _ = a * y * a⁻¹ * (a * u * a⁻¹) := h
      _ = a * (y * u) * a⁻¹ := by group
  simpa using h3

end CFSG.Quasithin.SteinbergCB

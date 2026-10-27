module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

public section

namespace CFSG.ShultStronglyClosedTI.MiscAlgebra

variable {G Ω : Type*} [Group G]

theorem commuting_regular_orbit_product_fixed_point_count [Finite Ω]
    (act : Ω → G → Ω) (act_one : ∀ ω, act ω 1 = ω)
    (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h))
    {K J : Subgroup G} {Δ Γ : Set Ω} (hΔΓ : IsCompl Δ Γ)
    (hKΓ : ∀ k ∈ K, ∀ γ ∈ Γ, act γ k ∈ Γ)
    (htrans : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, ∃ k ∈ K, act γ k = γ')
    (hfree : ∀ γ ∈ Γ, ∀ k ∈ K, act γ k = γ → k = 1)
    (hJK : J ≤ Subgroup.centralizer K) (hJΔ : ∀ j ∈ J, ∀ δ ∈ Δ, act δ j = δ)
    {x j : G} (hx : x ∈ K) (hj : j ∈ J) :
    Nat.card {ω | act ω (j * x) = ω} =
        Nat.card {δ | δ ∈ Δ ∧ act δ x = δ} + Nat.card {γ | γ ∈ Γ ∧ act γ (j * x) = γ} ∧
    (Nat.card {ω | act ω (j * x) = ω} = Nat.card {δ | δ ∈ Δ ∧ act δ x = δ} ∨
      Nat.card {ω | act ω (j * x) = ω} =
        Nat.card {δ | δ ∈ Δ ∧ act δ x = δ} +
          Nat.card (K ⊓ Subgroup.centralizer {x} : Subgroup G)) ∧
    ∀ γ₀ ∈ Γ, (∃! d, d ∈ K ∧ act γ₀ j = act γ₀ d) ∧
      ∀ d ∈ K, act γ₀ j = act γ₀ d →
        ((∃ k ∈ K, k * x * k⁻¹ = d⁻¹) →
          Nat.card {γ | γ ∈ Γ ∧ act γ (j * x) = γ} =
            Nat.card (K ⊓ Subgroup.centralizer {x} : Subgroup G)) ∧
        ((¬ ∃ k ∈ K, k * x * k⁻¹ = d⁻¹) →
          Nat.card {γ | γ ∈ Γ ∧ act γ (j * x) = γ} = 0) := by
  obtain rfl : Γ = Δᶜ := hΔΓ.compl_eq.symm
  simp only [Nat.card_coe_set_eq]
  have act_inv : ∀ ω g, act (act ω g) g⁻¹ = ω := fun ω g => by
    rw [act_mul, mul_inv_cancel, act_one]
  have huniq : ∀ γ ∈ Δᶜ, ∀ a ∈ K, ∀ b ∈ K, act γ a = act γ b → a = b := by
    intro γ hγ a ha b hb hab
    have h := hfree γ hγ (a * b⁻¹) (K.mul_mem ha (K.inv_mem hb))
      (by rw [← act_mul, hab, act_inv])
    exact mul_inv_eq_one.mp h
  have hjΓ : ∀ γ ∈ Δᶜ, act γ j ∈ Δᶜ := by
    intro γ hγ hγj
    apply hγ
    have h := hJΔ j⁻¹ (J.inv_mem hj) (act γ j) hγj
    rw [act_inv] at h
    rwa [h]
  have hΔ : ∀ δ ∈ Δ, act δ (j * x) = act δ x := fun δ hδ => by
    rw [← act_mul, hJΔ j hj δ hδ]
  have hsplit : {ω | act ω (j * x) = ω} =
      {δ | δ ∈ Δ ∧ act δ x = δ} ∪ {γ | γ ∈ Δᶜ ∧ act γ (j * x) = γ} := by
    ext ω
    by_cases hω : ω ∈ Δ
    · simp [hω, hΔ ω hω]
    · simp [hω]
  have hsum : {ω | act ω (j * x) = ω}.ncard =
      {δ | δ ∈ Δ ∧ act δ x = δ}.ncard + {γ | γ ∈ Δᶜ ∧ act γ (j * x) = γ}.ncard := by
    rw [hsplit]
    exact Set.ncard_union_eq (Set.disjoint_left.mpr fun ω h1 h2 => h2.1 h1.1)
  have hΓcount : ∀ γ₀ ∈ Δᶜ, ∀ d ∈ K, act γ₀ j = act γ₀ d →
      ((∃ k ∈ K, k * x * k⁻¹ = d⁻¹) →
        {γ | γ ∈ Δᶜ ∧ act γ (j * x) = γ}.ncard =
          ((K ⊓ Subgroup.centralizer {x} : Subgroup G) : Set G).ncard) ∧
      ((¬ ∃ k ∈ K, k * x * k⁻¹ = d⁻¹) → {γ | γ ∈ Δᶜ ∧ act γ (j * x) = γ}.ncard = 0) := by
    intro γ₀ hγ₀ d hd hjd
    have hcomp : ∀ k ∈ K, act (act γ₀ k) (j * x) = act γ₀ (d * (k * x)) := by
      intro k hk
      have hkj : k * j = j * k := Subgroup.mem_centralizer_iff.mp (hJK hj) k hk
      rw [act_mul, ← mul_assoc, hkj, mul_assoc, ← act_mul, hjd, act_mul]
    have hfix : ∀ k ∈ K, act (act γ₀ k) (j * x) = act γ₀ k ↔ k * x * k⁻¹ = d⁻¹ := by
      intro k hk
      rw [hcomp k hk]
      constructor
      · intro h
        have h' := huniq γ₀ hγ₀ _ (K.mul_mem hd (K.mul_mem hk hx)) k hk h
        calc k * x * k⁻¹ = d⁻¹ * (d * (k * x)) * k⁻¹ := by group
          _ = d⁻¹ := by rw [h']; group
      · intro h
        have hd' : d = (k * x * k⁻¹)⁻¹ := by rw [h, inv_inv]
        rw [hd']
        group
    have himage : {γ | γ ∈ Δᶜ ∧ act γ (j * x) = γ} =
        (fun k => act γ₀ k) '' {k | k ∈ K ∧ k * x * k⁻¹ = d⁻¹} := by
      ext γ
      constructor
      · rintro ⟨hγ, hγfix⟩
        obtain ⟨k, hk, rfl⟩ := htrans γ₀ hγ₀ γ hγ
        exact ⟨k, ⟨hk, (hfix k hk).mp hγfix⟩, rfl⟩
      · rintro ⟨k, ⟨hk, hkx⟩, rfl⟩
        exact ⟨hKΓ k hk γ₀ hγ₀, (hfix k hk).mpr hkx⟩
    have hinj : Set.InjOn (fun k => act γ₀ k) {k | k ∈ K ∧ k * x * k⁻¹ = d⁻¹} :=
      fun a ha b hb hab => huniq γ₀ hγ₀ a ha.1 b hb.1 hab
    rw [himage, hinj.ncard_image]
    refine ⟨?_, fun hno => ?_⟩
    · rintro ⟨k₀, hk₀, hk₀x⟩
      have hcoset : {k | k ∈ K ∧ k * x * k⁻¹ = d⁻¹} =
          (fun c => k₀ * c) '' ((K ⊓ Subgroup.centralizer {x} : Subgroup G) : Set G) := by
        ext k
        constructor
        · rintro ⟨hk, hkx⟩
          have h : k * x * k⁻¹ = k₀ * x * k₀⁻¹ := hkx.trans hk₀x.symm
          refine ⟨k₀⁻¹ * k, Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem hk₀) hk,
            Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, by group⟩
          calc k₀⁻¹ * k * x = k₀⁻¹ * (k * x * k⁻¹) * k := by group
            _ = x * (k₀⁻¹ * k) := by rw [h]; group
        · rintro ⟨c, hc, rfl⟩
          obtain ⟨hcK, hcx⟩ := Subgroup.mem_inf.mp hc
          rw [Subgroup.mem_centralizer_singleton_iff] at hcx
          refine ⟨K.mul_mem hk₀ hcK, ?_⟩
          calc k₀ * c * x * (k₀ * c)⁻¹ = k₀ * (c * x) * c⁻¹ * k₀⁻¹ := by group
            _ = d⁻¹ := by rw [hcx, ← hk₀x]; group
      rw [hcoset, Set.ncard_image_of_injective _ (mul_right_injective k₀)]
    · have hempty : {k | k ∈ K ∧ k * x * k⁻¹ = d⁻¹} = ∅ :=
        Set.eq_empty_of_forall_notMem fun k hk => hno ⟨k, hk.1, hk.2⟩
      rw [hempty, Set.ncard_empty]
  have hd : ∀ γ₀ ∈ Δᶜ, ∃! d, d ∈ K ∧ act γ₀ j = act γ₀ d := by
    intro γ₀ hγ₀
    obtain ⟨d, hd, hdj⟩ := htrans γ₀ hγ₀ (act γ₀ j) (hjΓ γ₀ hγ₀)
    exact ⟨d, ⟨hd, hdj.symm⟩, fun d' hd' => huniq γ₀ hγ₀ d' hd'.1 d hd (hd'.2.symm.trans hdj.symm)⟩
  have hC : Nat.card (K ⊓ Subgroup.centralizer {x} : Subgroup G) =
      ((K ⊓ Subgroup.centralizer {x} : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  refine ⟨hsum, ?_, fun γ₀ hγ₀ => ⟨hd γ₀ hγ₀, fun d hd' hjd => ?_⟩⟩
  · rw [hsum, hC]
    by_cases hΓ : (Δᶜ : Set Ω).Nonempty
    · obtain ⟨γ₀, hγ₀⟩ := hΓ
      obtain ⟨d, ⟨hd', hjd⟩, -⟩ := hd γ₀ hγ₀
      by_cases hconj : ∃ k ∈ K, k * x * k⁻¹ = d⁻¹
      · exact Or.inr (by rw [(hΓcount γ₀ hγ₀ d hd' hjd).1 hconj])
      · exact Or.inl (by rw [(hΓcount γ₀ hγ₀ d hd' hjd).2 hconj, add_zero])
    · left
      rw [Set.not_nonempty_iff_eq_empty] at hΓ
      simp [hΓ]
  · rw [hC]
    exact hΓcount γ₀ hγ₀ d hd' hjd

theorem commuting_regular_orbit_product_fixed_point_count_smul [MulAction G Ω] [Finite Ω]
    {K J : Subgroup G} {Δ Γ : Set Ω} (hΔΓ : IsCompl Δ Γ)
    (hKΓ : ∀ k ∈ K, ∀ γ ∈ Γ, k • γ ∈ Γ)
    (htrans : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, ∃ k ∈ K, k • γ = γ')
    (hfree : ∀ γ ∈ Γ, ∀ k ∈ K, k • γ = γ → k = 1)
    (hJK : J ≤ Subgroup.centralizer K) (hJΔ : ∀ j ∈ J, ∀ δ ∈ Δ, j • δ = δ)
    {x j : G} (hx : x ∈ K) (hj : j ∈ J) :
    Nat.card {ω : Ω | (j * x) • ω = ω} =
        Nat.card {δ | δ ∈ Δ ∧ x • δ = δ} + Nat.card {γ | γ ∈ Γ ∧ (j * x) • γ = γ} ∧
    (Nat.card {ω : Ω | (j * x) • ω = ω} = Nat.card {δ | δ ∈ Δ ∧ x • δ = δ} ∨
      Nat.card {ω : Ω | (j * x) • ω = ω} =
        Nat.card {δ | δ ∈ Δ ∧ x • δ = δ} +
          Nat.card (K ⊓ Subgroup.centralizer {x} : Subgroup G)) ∧
    ∀ γ₀ ∈ Γ, (∃! d, d ∈ K ∧ j • γ₀ = d • γ₀) ∧
      ∀ d ∈ K, j • γ₀ = d • γ₀ →
        ((∃ k ∈ K, k * x * k⁻¹ = d⁻¹) →
          Nat.card {γ | γ ∈ Γ ∧ (j * x) • γ = γ} =
            Nat.card (K ⊓ Subgroup.centralizer {x} : Subgroup G)) ∧
        ((¬ ∃ k ∈ K, k * x * k⁻¹ = d⁻¹) →
          Nat.card {γ | γ ∈ Γ ∧ (j * x) • γ = γ} = 0) := by
  have hfix : ∀ g : G, ∀ ω : Ω, g⁻¹ • ω = ω ↔ g • ω = ω := fun g ω => by
    rw [inv_smul_eq_iff, eq_comm]
  have hjd : ∀ d ∈ K, ∀ γ : Ω, j⁻¹ • γ = d⁻¹ • γ ↔ j • γ = d • γ := by
    intro d hd γ
    have hdj : d * j = j * d := Subgroup.mem_centralizer_iff.mp (hJK hj) d hd
    constructor
    · intro h
      have hγ : (d * j⁻¹) • γ = γ := by rw [mul_smul, h, smul_inv_smul]
      calc j • γ = j • (d * j⁻¹) • γ := by rw [hγ]
        _ = d • γ := by rw [smul_smul, ← mul_assoc, ← hdj, mul_inv_cancel_right]
    · intro h
      have hγ : (d⁻¹ * j) • γ = γ := by rw [mul_smul, h, inv_smul_smul]
      calc j⁻¹ • γ = j⁻¹ • (d⁻¹ * j) • γ := by rw [hγ]
        _ = d⁻¹ • γ := by
          rw [smul_smul, ← mul_assoc, ← mul_inv_rev, hdj, mul_inv_rev, inv_mul_cancel_right]
  obtain ⟨h1, h2, h3⟩ := commuting_regular_orbit_product_fixed_point_count (fun ω g => g⁻¹ • ω)
    (fun ω => by rw [inv_one, one_smul])
    (fun ω g h => by rw [mul_inv_rev, mul_smul])
    hΔΓ (fun k hk γ hγ => hKΓ k⁻¹ (K.inv_mem hk) γ hγ)
    (fun γ hγ γ' hγ' => by
      obtain ⟨k, hk, rfl⟩ := htrans γ hγ γ' hγ'
      exact ⟨k⁻¹, K.inv_mem hk, by rw [inv_inv]⟩)
    (fun γ hγ k hk hkγ => hfree γ hγ k hk ((hfix k γ).mp hkγ))
    hJK (fun j hj δ hδ => (hfix j δ).mpr (hJΔ j hj δ hδ)) hx hj
  simp only [hfix] at h1 h2 h3
  refine ⟨h1, h2, fun γ₀ hγ₀ => ⟨?_, fun d hd hd₀ => h3 γ₀ hγ₀ |>.2 d hd ((hjd d hd γ₀).mpr hd₀)⟩⟩
  obtain ⟨d, ⟨hd, hd₀⟩, huniq⟩ := (h3 γ₀ hγ₀).1
  exact ⟨d, ⟨hd, (hjd d hd γ₀).mp hd₀⟩,
    fun d' hd' => huniq d' ⟨hd'.1, (hjd d' hd'.1 γ₀).mpr hd'.2⟩⟩

end CFSG.ShultStronglyClosedTI.MiscAlgebra

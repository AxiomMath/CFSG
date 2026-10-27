module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.H13.QRCBenderCore

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup

section Factors

variable {A : Type*} [Group A]

theorem le_normalizer_of_commute {K₁ K₂ : Subgroup A}
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) : K₂ ≤ normalizer (K₁ : Set A) := fun b hb =>
  mem_normalizer_iff.2 fun y => by
    constructor
    · intro hy
      rw [← hc y hy b hb, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h2 := hc _ hy b hb
      have h3 : y = b * y * b⁻¹ := by
        calc y = b⁻¹ * ((b * y * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * y * b⁻¹)) := by rw [h2]
          _ = b * y * b⁻¹ := by group
      rw [h3]
      exact hy

theorem mem_of_centralizes_factor {K₁ K₂ : Subgroup A} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hZ : ∀ z ∈ K₁, (∀ y ∈ K₁, z * y = y * z) → z = 1) {x : A} (hx : x ∈ K₁ ⊔ K₂)
    (hxc : ∀ y ∈ K₁, x * y = y * x) : x ∈ K₂ := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K₁ K₂
    (le_normalizer_of_commute hc)] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := hx
  beta_reduce at hxc ⊢
  have hu1 : u = 1 := by
    refine hZ u hu fun y hy => ?_
    have h1 := hxc y hy
    have h2 : v * y = y * v := (hc y hy v hv).symm
    calc u * y = u * (v * y) * v⁻¹ := by rw [h2]; group
      _ = (u * v) * y * v⁻¹ := by group
      _ = y * (u * v) * v⁻¹ := by rw [h1]
      _ = y * u := by group
  rw [hu1, one_mul]
  exact hv

theorem le_normalizer_inf {X Y Z : Subgroup A} (hX : Z ≤ normalizer (X : Set A))
    (hY : Z ≤ normalizer (Y : Set A)) : Z ≤ normalizer ((X ⊓ Y : Subgroup A) : Set A) :=
  fun _ hz => mem_normalizer_iff.2 fun y =>
    ⟨fun h => ⟨(mem_normalizer_iff.1 (hX hz) y).1 h.1, (mem_normalizer_iff.1 (hY hz) y).1 h.2⟩,
      fun h => ⟨(mem_normalizer_iff.1 (hX hz) y).2 h.1, (mem_normalizer_iff.1 (hY hz) y).2 h.2⟩⟩

theorem eq_of_normalized_of_simple {K N : Subgroup A} [IsSimpleGroup K] (hNK : N ≤ K)
    (hn : K ≤ normalizer (N : Set A)) (hN : N ≠ ⊥) : N = K := by
  have hsub : (N.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hNK).2 hn
  rcases hsub.eq_bot_or_eq_top with h | h
  · exact absurd (disjoint_self.1 ((subgroupOf_eq_bot.1 h).mono_right hNK)) hN
  · exact le_antisymm hNK (subgroupOf_eq_top.1 h)

variable [Finite A]

theorem conj_factor_eq_or {K₁ K₂ : Subgroup A} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hn : (K₁ ⊔ K₂).Normal) [IsSimpleGroup K₁] (hZ : ∀ z ∈ K₁, (∀ y ∈ K₁, z * y = y * z) → z = 1)
    (hcard : Nat.card K₁ = Nat.card K₂) (a : A) :
    K₁.map (MulAut.conj a).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj a).toMonoidHom = K₂ := by
  set N := K₁.map (MulAut.conj a).toMonoidHom with hNdef
  have hKN₁ : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set A) :=
    sup_le le_normalizer (le_normalizer_of_commute hc)
  have hNK : N ≤ K₁ ⊔ K₂ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hn.conj_mem y (mem_sup_left hy) a
  have hKN : K₁ ⊔ K₂ ≤ normalizer (N : Set A) := by
    intro k hk
    have hk' : a⁻¹ * k * a ∈ K₁ ⊔ K₂ := by
      have := hn.conj_mem k hk a⁻¹
      rwa [inv_inv] at this
    refine mem_normalizer_iff.2 fun y => ⟨?_, ?_⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(a⁻¹ * k * a) * z * (a⁻¹ * k * a)⁻¹,
        (mem_normalizer_iff.1 (hKN₁ hk') z).1 hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨z, hz, hzy⟩
      refine ⟨(a⁻¹ * k * a)⁻¹ * z * (a⁻¹ * k * a), ?_, ?_⟩
      · have h1 := (mem_normalizer_iff.1 (hKN₁ (inv_mem hk')) z).1 hz
        rwa [inv_inv] at h1
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy ⊢
        rw [show a * ((a⁻¹ * k * a)⁻¹ * z * (a⁻¹ * k * a)) * a⁻¹ = k⁻¹ * (a * z * a⁻¹) * k by
          group, hzy]
        group
  have hcardN : Nat.card N = Nat.card K₁ :=
    card_map_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective
  by_cases h1 : N ⊓ K₁ = ⊥
  · right
    have hNK₂ : N ≤ K₂ := by
      intro y hy
      refine mem_of_centralizes_factor hc hZ (hNK hy) fun z hz => ?_
      have hcomm : y * z * y⁻¹ * z⁻¹ ∈ N ⊓ K₁ := by
        refine ⟨?_, ?_⟩
        · have h2 := (mem_normalizer_iff.1 (hKN (mem_sup_left hz)) y⁻¹).1 (N.inv_mem hy)
          rw [show y * z * y⁻¹ * z⁻¹ = y * (z * y⁻¹ * z⁻¹) by group]
          exact N.mul_mem hy h2
        · have h2 := (mem_normalizer_iff.1 (hKN₁ (hNK hy)) z).1 hz
          exact K₁.mul_mem h2 (K₁.inv_mem hz)
      rw [h1, mem_bot] at hcomm
      calc y * z = y * z * y⁻¹ * z⁻¹ * z * y := by group
        _ = z * y := by rw [hcomm, one_mul]
    exact eq_of_le_of_card_ge hNK₂ (by rw [hcardN, hcard])
  · left
    have h2 : N ⊓ K₁ = K₁ := by
      have : IsSimpleGroup K₁ := inferInstance
      exact eq_of_normalized_of_simple inf_le_right
        (le_normalizer_inf ((le_sup_left : K₁ ≤ K₁ ⊔ K₂).trans hKN) le_normalizer) h1
    have hK₁N : K₁ ≤ N := h2 ▸ inf_le_left
    exact (eq_of_le_of_card_ge hK₁N (by rw [hcardN])).symm

omit [Finite A] in
theorem le_sup_projections {K₁ K₂ E : Subgroup A} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hE : E ≤ K₁ ⊔ K₂) : E ≤ (E ⊔ K₂) ⊓ K₁ ⊔ (E ⊔ K₁) ⊓ K₂ := by
  intro e he
  have h1 := hE he
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K₁ K₂
    (le_normalizer_of_commute hc)] at h1
  obtain ⟨u, hu, v, hv, rfl⟩ := h1
  beta_reduce at he ⊢
  refine mul_mem_sup ⟨?_, hu⟩ ⟨?_, hv⟩
  · have h2 := mul_mem_sup (S := E) (T := K₂) he (inv_mem hv)
    rwa [mul_inv_cancel_right] at h2
  · have h2 := mul_mem_sup (S := E) (T := K₁) he (inv_mem hu)
    rw [hc u hu v hv] at h2
    rwa [mul_inv_cancel_right] at h2

end Factors

end CFSG.Quasithin.H13.QRC

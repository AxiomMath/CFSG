module

public import CFSG.Quasithin.EmptyFaithful.S146zJAlg
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

section Cnt

variable {V : Type*} [CommGroup V] [Finite V]

theorem card_fix_sup_le (σ : MulAut V) (W₁ W₂ : Subgroup V) (hinf : W₁ ⊓ W₂ = ⊥)
    (h1 : ∀ w ∈ W₁, σ w ∈ W₁) (h2 : ∀ w ∈ W₂, σ w ∈ W₂) :
    Nat.card ↥(fixSubOf σ ⊓ (W₁ ⊔ W₂)) ≤
      Nat.card ↥(fixSubOf σ ⊓ W₁) * Nat.card ↥(fixSubOf σ ⊓ W₂) := by
  classical
  have hdec : ∀ x ∈ fixSubOf σ ⊓ (W₁ ⊔ W₂), ∃ y ∈ fixSubOf σ ⊓ W₁, ∃ z ∈ fixSubOf σ ⊓ W₂,
      y * z = x := by
    rintro x ⟨hxf, hxs⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hxs
    have hσ : σ y * σ z = y * z := by rw [← map_mul]; exact hxf
    have hσy : σ y ∈ W₁ := h1 y hy
    have hσz : σ z ∈ W₂ := h2 z hz
    have e : y⁻¹ * σ y = z * (σ z)⁻¹ := by
      have : σ y * σ z = y * z := hσ
      calc y⁻¹ * σ y = y⁻¹ * σ y * (σ z * (σ z)⁻¹) := by rw [mul_inv_cancel, mul_one]
        _ = y⁻¹ * (σ y * σ z) * (σ z)⁻¹ := by group
        _ = y⁻¹ * (y * z) * (σ z)⁻¹ := by rw [this]
        _ = z * (σ z)⁻¹ := by group
    have hmem : y⁻¹ * σ y ∈ W₁ ⊓ W₂ :=
      ⟨W₁.mul_mem (W₁.inv_mem hy) hσy, e ▸ W₂.mul_mem hz (W₂.inv_mem hσz)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hy1 : σ y = y := by
      have := congrArg (fun t => y * t) hmem
      simpa using this
    have hz1 : σ z = z := by
      have h3 : y * σ z = y * z := by rw [← hy1] at hσ ⊢; simpa [hy1] using hσ
      exact mul_left_cancel h3
    exact ⟨y, ⟨hy1, hy⟩, z, ⟨hz1, hz⟩, rfl⟩
  choose! y hy z hz hyz using hdec
  let f : ↥(fixSubOf σ ⊓ (W₁ ⊔ W₂)) → ↥(fixSubOf σ ⊓ W₁) × ↥(fixSubOf σ ⊓ W₂) := fun x =>
    (⟨y x, hy x x.2⟩, ⟨z x, hz x x.2⟩)
  have hinj : Function.Injective f := by
    intro x x' hxx
    have h1' : y x = y x' := congrArg (fun q => (q.1 : V)) hxx
    have h2' : z x = z x' := congrArg (fun q => (q.2 : V)) hxx
    apply Subtype.ext
    rw [← hyz x x.2, ← hyz x' x'.2, h1', h2']
  have h3 := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod] at h3
  exact h3

theorem card_fix_swap_le (σ : MulAut V) (W₁ W₂ : Subgroup V) (hinf : W₁ ⊓ W₂ = ⊥)
    (h1 : ∀ w ∈ W₁, σ w ∈ W₂) (h2 : ∀ w ∈ W₂, σ w ∈ W₁) :
    Nat.card ↥(fixSubOf σ ⊓ (W₁ ⊔ W₂)) ≤ Nat.card ↥W₂ := by
  classical
  have hdec : ∀ x ∈ fixSubOf σ ⊓ (W₁ ⊔ W₂), ∃ y ∈ W₁, ∃ z ∈ W₂, y * z = x ∧ y = σ z := by
    rintro x ⟨hxf, hxs⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hxs
    have hσ : σ y * σ z = y * z := by rw [← map_mul]; exact hxf
    have hσy : σ y ∈ W₂ := h1 y hy
    have hσz : σ z ∈ W₁ := h2 z hz
    have e : y⁻¹ * σ z = z * (σ y)⁻¹ := by
      calc y⁻¹ * σ z = y⁻¹ * σ z * (σ y * (σ y)⁻¹) := by rw [mul_inv_cancel, mul_one]
        _ = y⁻¹ * (σ y * σ z) * (σ y)⁻¹ := by rw [mul_comm (σ y) (σ z)]; group
        _ = y⁻¹ * (y * z) * (σ y)⁻¹ := by rw [hσ]
        _ = z * (σ y)⁻¹ := by group
    have hmem : y⁻¹ * σ z ∈ W₁ ⊓ W₂ :=
      ⟨W₁.mul_mem (W₁.inv_mem hy) hσz, e ▸ W₂.mul_mem hz (W₂.inv_mem hσy)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact ⟨y, hy, z, hz, rfl, inv_mul_eq_one.mp hmem⟩
  choose! y hy z hz hyz hyσ using hdec
  let f : ↥(fixSubOf σ ⊓ (W₁ ⊔ W₂)) → ↥W₂ := fun x => ⟨z x, hz x x.2⟩
  have hinj : Function.Injective f := by
    intro x x' hxx
    have h2' : z x = z x' := congrArg Subtype.val hxx
    have h1' : y x = y x' := by rw [hyσ x x.2, hyσ x' x'.2, h2']
    apply Subtype.ext
    rw [← (hyz x x.2), ← (hyz x' x'.2), h1', h2']
  exact Nat.card_le_card_of_injective f hinj

omit [Finite V] in
theorem decomp_unique {W₁ W₂ : Subgroup V} (hinf : W₁ ⊓ W₂ = ⊥) {a a' b b' : V} (ha : a ∈ W₁)
    (ha' : a' ∈ W₁) (hb : b ∈ W₂) (hb' : b' ∈ W₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have e : a / a' = b' / b := by
    rw [div_eq_div_iff_mul_eq_mul]
    rw [mul_comm b' a']
    exact h
  have hmem : a / a' ∈ W₁ ⊓ W₂ := ⟨W₁.div_mem ha ha', e ▸ W₂.div_mem hb' hb⟩
  rw [hinf, Subgroup.mem_bot, div_eq_one] at hmem
  refine ⟨hmem, ?_⟩
  rw [hmem] at h
  exact mul_left_cancel h

theorem card_fix_swap_inter_le (σ y : MulAut V) (W₁ W₂ : Subgroup V) (hinf : W₁ ⊓ W₂ = ⊥)
    (h1 : ∀ w ∈ W₁, σ w ∈ W₂) (h2 : ∀ w ∈ W₂, σ w ∈ W₁)
    (hy1 : ∀ w ∈ W₁, y w ∈ W₁) (hy2 : ∀ w ∈ W₂, y w ∈ W₂) :
    Nat.card ↥(fixSubOf σ ⊓ fixSubOf y ⊓ (W₁ ⊔ W₂)) ≤ Nat.card ↥(fixSubOf y ⊓ W₂) := by
  classical
  have hdec : ∀ x ∈ fixSubOf σ ⊓ fixSubOf y ⊓ (W₁ ⊔ W₂),
      ∃ a ∈ W₁, ∃ b ∈ fixSubOf y ⊓ W₂, a * b = x ∧ a = σ b := by
    rintro x ⟨⟨hxσ, hxy⟩, hxs⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hxs
    have hσ : σ a * σ b = a * b := by rw [← map_mul]; exact hxσ
    have hy : y a * y b = a * b := by rw [← map_mul]; exact hxy
    have hσa : σ a ∈ W₂ := h1 a ha
    have hσb : σ b ∈ W₁ := h2 b hb
    have hu := decomp_unique hinf hσb ha hσa hb (by rw [mul_comm (σ b) (σ a), hσ])
    have hu' := decomp_unique hinf (hy1 a ha) ha (hy2 b hb) hb hy
    exact ⟨a, ha, b, ⟨hu'.2, hb⟩, rfl, hu.1.symm⟩
  choose! a ha b hb hab haσ using hdec
  let f : ↥(fixSubOf σ ⊓ fixSubOf y ⊓ (W₁ ⊔ W₂)) → ↥(fixSubOf y ⊓ W₂) := fun x =>
    ⟨b x, hb x x.2⟩
  have hinj : Function.Injective f := by
    intro x x' hxx
    have h2' : b x = b x' := congrArg Subtype.val hxx
    have h1' : a x = a x' := by rw [haσ x x.2, haσ x' x'.2, h2']
    apply Subtype.ext
    rw [← hab x x.2, ← hab x' x'.2, h1', h2']
  exact Nat.card_le_card_of_injective f hinj

theorem index_ge_of_inf_le (F W : Subgroup V) {m : ℕ} (hfix : Nat.card ↥(F ⊓ W) ≤ m) :
    Nat.card ↥W ≤ F.index * m := by
  have h1 := Subgroup.relIndex_mul_card F W
  have h2 : F.relIndex W ∣ F.index := Subgroup.relIndex_dvd_index_of_normal _ _
  have h3 : F.relIndex W ≤ F.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h2
  rw [← h1]
  exact Nat.mul_le_mul h3 hfix

end Cnt

end CFSG.Quasithin

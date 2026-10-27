module

import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin

namespace E217R4

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_of_map_eq {H : Subgroup Γ} {g : Γ}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have : y = x := mul_left_cancel (mul_right_cancel hyx')
    rwa [← this]

theorem zpowers_eq_of_mem {a x : Γ} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hxa : x ∈ Subgroup.zpowers a) : Subgroup.zpowers x = Subgroup.zpowers a := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers a := (Subgroup.zpowers_le).2 hxa
  have hc : ∀ y : Γ, y ^ 3 = 1 → y ≠ 1 → Nat.card (Subgroup.zpowers y) = 3 := fun y hy3 hy1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hy3 hy1
  have : Finite ↥(Subgroup.zpowers a) :=
    Nat.finite_of_card_ne_zero (by rw [hc a ha3 ha1]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc a ha3 ha1, hc x hx3 hx1])

theorem exists_mul_of_mem_sup {K₁ K₂ : Subgroup Γ} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    {c : Γ} (hc' : c ∈ K₁ ⊔ K₂) : ∃ x ∈ K₁, ∃ y ∈ K₂, x * y = c := by
  have hc'' : c ∈ (↑(K₁ ⊔ K₂) : Set Γ) := hc'
  rw [sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left K₂ K₁ ?_] at hc''
  · obtain ⟨y, hy, x, hx, rfl⟩ := hc''
    exact ⟨x, hx, y, hy, hc x hx y hy⟩
  · exact (show K₁ ≤ Subgroup.centralizer (K₂ : Set Γ) from fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun b hb => (hc a ha b hb).symm).trans
      (Subgroup.centralizer_le_normalizer _)

theorem eq_of_mul_eq_of_inf_eq_bot {K₁ K₂ : Subgroup Γ} (hd : K₁ ⊓ K₂ = ⊥) {x₁ y₁ x₂ y₂ : Γ}
    (hx₁ : x₁ ∈ K₁) (hy₁ : y₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (hy₂ : y₂ ∈ K₂) (h : x₁ * x₂ = y₁ * y₂) :
    x₁ = y₁ ∧ x₂ = y₂ := by
  have h2 : y₁⁻¹ * x₁ = y₂ * x₂⁻¹ := by
    calc y₁⁻¹ * x₁ = y₁⁻¹ * (x₁ * x₂) * x₂⁻¹ := by group
      _ = y₂ * x₂⁻¹ := by rw [h]; group
  have hw : y₁⁻¹ * x₁ ∈ K₁ ⊓ K₂ :=
    ⟨K₁.mul_mem (K₁.inv_mem hy₁) hx₁, h2 ▸ K₂.mul_mem hy₂ (K₂.inv_mem hx₂)⟩
  rw [hd, Subgroup.mem_bot] at hw
  have hx : x₁ = y₁ := by
    calc x₁ = y₁ * (y₁⁻¹ * x₁) := by group
      _ = y₁ := by rw [hw]; group
  refine ⟨hx, ?_⟩
  rw [hx] at h
  exact mul_left_cancel h

theorem card_sup_eq_mul {K₁ K₂ : Subgroup Γ} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hd : K₁ ⊓ K₂ = ⊥) : Nat.card ↥(K₁ ⊔ K₂) = Nat.card K₁ * Nat.card K₂ := by
  let f : ↥K₁ × ↥K₂ → ↥(K₁ ⊔ K₂) := fun p =>
    ⟨(p.1 : Γ) * (p.2 : Γ), Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
      have h1 : (x₁ : Γ) * x₂ = y₁ * y₂ := congrArg Subtype.val h
      obtain ⟨hx, hy⟩ := eq_of_mul_eq_of_inf_eq_bot hd x₁.2 y₁.2 x₂.2 y₂.2 h1
      exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
    · rintro ⟨c, hc'⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hc hc'
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

end E217R4

end CFSG.Quasithin

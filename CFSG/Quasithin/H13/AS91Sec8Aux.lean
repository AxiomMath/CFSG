module

public import CFSG.Quasithin.H13.AS91Sec5Geom

public section

namespace CFSG.Quasithin.H13.AS91

open MulAction
open scoped Pointwise

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

theorem exists_normalizer_smul_of_fixed (B : Subgroup G) [Finite B] {y₁ y₂ : X}
    (h₁ : ∃ b ∈ B, b • y₂ = y₁) (hfix : ∀ g ∈ B, g • y₂ = y₂ → g • y₁ = y₁) :
    ∃ n ∈ B, n ∈ Subgroup.normalizer ((B ⊓ stabilizer G y₂ : Subgroup G) : Set G) ∧
      n • y₂ = y₁ := by
  obtain ⟨b, hb, hby⟩ := h₁
  have hmem : ∀ p : G, p ∈ (B ⊓ stabilizer G y₂ : Subgroup G) ↔ p ∈ B ∧ p • y₂ = y₂ := by
    intro p
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  have hmaps : ∀ p : G, p ∈ (B ⊓ stabilizer G y₂ : Subgroup G) →
      b⁻¹ * p * b ∈ (B ⊓ stabilizer G y₂ : Subgroup G) := by
    intro p hp
    obtain ⟨hpB, hpy⟩ := (hmem p).mp hp
    have hy1 : p • y₁ = y₁ := hfix p hpB hpy
    rw [hmem]
    refine ⟨B.mul_mem (B.mul_mem (B.inv_mem hb) hpB) hb, ?_⟩
    rw [mul_smul, hby, mul_smul, hy1, ← hby, ← mul_smul, inv_mul_cancel, one_smul]
  haveI : Finite (B ⊓ stabilizer G y₂ : Subgroup G) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : B ⊓ stabilizer G y₂ ≤ B))
      (Subgroup.inclusion_injective _)
  let ψ : (B ⊓ stabilizer G y₂ : Subgroup G) → (B ⊓ stabilizer G y₂ : Subgroup G) :=
    fun p => ⟨b⁻¹ * (p : G) * b, hmaps (p : G) p.2⟩
  have hinj : Function.Injective ψ := by
    intro p q hpq
    have h' : b⁻¹ * (p : G) * b = b⁻¹ * (q : G) * b := congrArg Subtype.val hpq
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  have hsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hinj
  have hcov : ∀ h : G, h ∈ (B ⊓ stabilizer G y₂ : Subgroup G) →
      b * h * b⁻¹ ∈ (B ⊓ stabilizer G y₂ : Subgroup G) := by
    intro h hh
    obtain ⟨p, hp⟩ := hsurj ⟨h, hh⟩
    have hph : b⁻¹ * (p : G) * b = h := congrArg Subtype.val hp
    have hbh : b * h * b⁻¹ = (p : G) := by
      rw [← hph]
      simp [mul_assoc]
    rw [hbh]
    exact p.2
  refine ⟨b, hb, ?_, hby⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hcov h
  · intro hk
    have h2 := hmaps _ hk
    have e : b⁻¹ * (b * h * b⁻¹) * b = h := by simp [mul_assoc]
    rw [e] at h2
    exact h2

theorem mem_stabilizer_pair_iff {x y : X} (hxy : x ≠ y) (g : G) :
    g ∈ stabilizer G ({x, y} : Set X) ↔ (g • x = x ∧ g • y = y) ∨ (g • x = y ∧ g • y = x) := by
  rw [MulAction.mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton,
    Set.pair_eq_pair_iff]

end CFSG.Quasithin.H13.AS91

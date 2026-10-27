module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.Group

public section

namespace Subgroup

theorem eq_sup_zpowers_inf_of_fixed_inner_lifts {p : ℕ} {G : Type*} [Group G]
    {B L : Subgroup G} {x : G}
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hpow : ∀ a ∈ B, a ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (B : Set G), g ^ p = 1 → g ∈ B)
    (hker : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hLift : ∀ b ∈ B, ∃ a ∈ L, a ^ p = 1 ∧ (∀ c ∈ B, c * a = a * c) ∧
      ∀ l ∈ L, b * l * b⁻¹ = a * l * a⁻¹) :
    B = Subgroup.zpowers x ⊔ (B ⊓ L) := by
  apply le_antisymm
  · intro b hb
    obtain ⟨a, ha, hap, hfix, hact⟩ := hLift b hb
    let z := b * a⁻¹
    have hba : Commute b a := hfix b hb
    have hzp : z ^ p = 1 := by
      dsimp [z]
      rw [hba.inv_right.mul_pow, hpow b hb, inv_pow, hap, inv_one, one_mul]
    have hzB : z ∈ Subgroup.centralizer (B : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
      have hca : Commute c a := hfix c hc
      change c * (b * a⁻¹) = (b * a⁻¹) * c
      calc c * (b * a⁻¹) = (c * b) * a⁻¹ := by group
        _ = (b * c) * a⁻¹ := by rw [hcomm c hc b hb]
        _ = b * (c * a⁻¹) := by group
        _ = b * (a⁻¹ * c) := by rw [hca.inv_right.eq]
        _ = (b * a⁻¹) * c := by group
    have hzL : z ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      have hmem : a⁻¹ * l * a ∈ L := mul_mem (mul_mem (inv_mem ha) hl) ha
      have hconj : z * l * z⁻¹ = l := by
        dsimp [z]
        calc (b * a⁻¹) * l * (b * a⁻¹)⁻¹ = b * (a⁻¹ * l * a) * b⁻¹ := by group
          _ = a * (a⁻¹ * l * a) * a⁻¹ := hact _ hmem
          _ = l := by group
      calc l * z = (z * l * z⁻¹) * z := by rw [hconj]
        _ = z * l := by group
    have hz : z ∈ B := hSC z hzB hzp
    have hzX : z ∈ Subgroup.zpowers x := by
      rw [← hker]
      exact ⟨hz, hzL⟩
    have haB : a ∈ B := by
      have he : a = z⁻¹ * b := by dsimp [z]; group
      rw [he]
      exact mul_mem (inv_mem hz) hb
    have hzSup : z ∈ Subgroup.zpowers x ⊔ (B ⊓ L) :=
      (le_sup_left : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ (B ⊓ L)) hzX
    have haSup : a ∈ Subgroup.zpowers x ⊔ (B ⊓ L) :=
      (le_sup_right : B ⊓ L ≤ Subgroup.zpowers x ⊔ (B ⊓ L)) ⟨haB, ha⟩
    have he : b = z * a := by dsimp [z]; group
    rw [he]
    exact mul_mem hzSup haSup
  · refine sup_le ?_ inf_le_left
    rw [← hker]
    exact inf_le_left

end Subgroup

end

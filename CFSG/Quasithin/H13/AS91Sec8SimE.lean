module

public import CFSG.Quasithin.H13.AS91Sec8Defs
public import CFSG.Quasithin.H13.AS91Sec8Aux

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction
open scoped Pointwise

universe v u

variable {Gb : Type v} [Group Gb] {Xb : Type u} [MulAction Gb Xb]

private theorem mem_conj_iff {B : Subgroup Gb} {jz : Gb} (hjz : jz ∈ B) (h : Gb) :
    h ∈ B ↔ jz * h * jz⁻¹ ∈ B := by
  constructor
  · intro hh; exact mul_mem (mul_mem hjz hh) (inv_mem hjz)
  · intro hh
    have := mul_mem (mul_mem (inv_mem hjz) hh) hjz
    simpa [mul_assoc] using this

private theorem fix_conj_iff {yb : Xb} (jz h : Gb) :
    h • yb = yb ↔ (jz * h * jz⁻¹) • (jz • yb) = jz • yb := by
  rw [mul_smul, mul_smul, inv_smul_smul]
  exact ⟨fun hh => by rw [hh], fun hh => smul_left_cancel jz hh⟩

private theorem mem_conj_inf_stab {B : Subgroup Gb} {yb : Xb} {jz : Gb} (hjz : jz ∈ B) (h : Gb) :
    h ∈ B ⊓ stabilizer Gb yb ↔ jz * h * jz⁻¹ ∈ B ⊓ stabilizer Gb (jz • yb) := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff,
    ← mem_conj_iff hjz h, ← fix_conj_iff jz h]

theorem stab_inf_eq_of_fix [Finite Gb] {Ib : Subgroup Gb} {xb yb : Xb} (hV : HypV Ib xb yb)
    {ja jz : Gb} (hja : ja ∈ Ib ⊓ stabilizer Gb xb) (hjz : jz ∈ Ib ⊓ stabilizer Gb xb)
    (hfix : ∀ g ∈ Ib ⊓ stabilizer Gb xb, g • (jz • yb) = jz • yb → g • (ja • yb) = ja • yb) :
    stabilizer Gb xb ⊓ stabilizer Gb (ja • yb) = stabilizer Gb xb ⊓ stabilizer Gb (jz • yb) := by
  have h₁ : ∃ b ∈ Ib ⊓ stabilizer Gb xb, b • (jz • yb) = ja • yb := by
    refine ⟨ja * jz⁻¹, mul_mem hja (inv_mem hjz), ?_⟩
    rw [mul_smul, inv_smul_smul]
  obtain ⟨n, hnB, hnN, hn⟩ := exists_normalizer_smul_of_fixed (Ib ⊓ stabilizer Gb xb) h₁ hfix
  have hjzx : jz ∈ stabilizer Gb xb := (Subgroup.mem_inf.mp hjz).2
  have hnx : n ∈ stabilizer Gb xb := (Subgroup.mem_inf.mp hnB).2
  have hg₀B : jz⁻¹ * n * jz ∈ Ib ⊓ stabilizer Gb xb := mul_mem (mul_mem (inv_mem hjz) hnB) hjz
  have hg₀P : jz⁻¹ * n * jz ∈ Subgroup.normalizer
      ((Ib ⊓ stabilizer Gb xb ⊓ stabilizer Gb yb : Subgroup Gb) : Set Gb) := by
    rw [Subgroup.mem_normalizer_iff] at hnN ⊢
    intro h
    rw [mem_conj_inf_stab hjz h, mem_conj_inf_stab hjz (jz⁻¹ * n * jz * h * (jz⁻¹ * n * jz)⁻¹)]
    rw [show jz * (jz⁻¹ * n * jz * h * (jz⁻¹ * n * jz)⁻¹) * jz⁻¹ = n * (jz * h * jz⁻¹) * n⁻¹ by
      group]
    exact hnN _
  have hg₀G := hV.v4 _ hg₀B hg₀P
  have hnG : n ∈ Subgroup.normalizer ((stabilizer Gb xb ⊓ stabilizer Gb (jz • yb) :
      Subgroup Gb) : Set Gb) := by
    rw [Subgroup.mem_normalizer_iff] at hg₀G ⊢
    intro h
    have hc : ∀ h' : Gb, h' ∈ stabilizer Gb xb ⊓ stabilizer Gb (jz • yb) ↔
        jz⁻¹ * h' * jz ∈ stabilizer Gb xb ⊓ stabilizer Gb yb := by
      intro h'
      rw [mem_conj_inf_stab hjzx (jz⁻¹ * h' * jz)]
      simp [mul_assoc]
    rw [hc h, hc (n * h * n⁻¹)]
    rw [show jz⁻¹ * (n * h * n⁻¹) * jz = (jz⁻¹ * n * jz) * (jz⁻¹ * h * jz) * (jz⁻¹ * n * jz)⁻¹ by
      group]
    exact hg₀G _
  ext m
  rw [← hn]
  have hx1 : m ∈ stabilizer Gb xb ↔ n⁻¹ * m * n ∈ stabilizer Gb xb := by
    have := mem_conj_iff (inv_mem hnx) m
    simpa using this
  have hy1 : m ∈ stabilizer Gb (n • (jz • yb)) ↔ n⁻¹ * m * n ∈ stabilizer Gb (jz • yb) := by
    rw [mem_stabilizer_iff, mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]
  have hm : m ∈ stabilizer Gb xb ⊓ stabilizer Gb (n • (jz • yb)) ↔
      n⁻¹ * m * n ∈ stabilizer Gb xb ⊓ stabilizer Gb (jz • yb) := by
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hx1, hy1]
  rw [hm]
  have := hnG
  rw [Subgroup.mem_normalizer_iff] at this
  have h2 := this (n⁻¹ * m * n)
  rw [show n * (n⁻¹ * m * n) * n⁻¹ = m by group] at h2
  exact h2

end CFSG.Quasithin.H13.AS91

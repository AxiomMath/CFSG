module

public import CFSG.Quasithin.EmptyFaithful.SzC4Sl4Rad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzC4

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.Quasithin.A38c10
  CFSG.Quasithin.S15223P4.C.Nat4 CFSG.LieType.SteinbergBR.BlockPar
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem gb1_mem : gb1 ∈ QI 4 {1} := (mem_QI_one_iff (m := 3)).2 fun i => by fin_cases i <;> rfl

theorem gb3_mem : gb3 ∈ QI 4 {3} := by
  rw [QI_four_three_eq, mem_stabilizer_flagSpace_iff]
  intro i j hi hj
  have hi3 : i = 3 := Fin.ext (by have := i.2; omega)
  subst hi3
  fin_cases j <;> first | rfl | (exfalso; simp at hj)

theorem gb1_pow : gb1 ^ 7 = 1 := by
  apply Subtype.ext
  show gb1M ^ 7 = 1
  decide

theorem gb3_pow : gb3 ^ 7 = 1 := by
  apply Subtype.ext
  show gb3M ^ 7 = 1
  decide

theorem gb3_eq : gb3 = wb * gb1 * wb⁻¹ := by
  have h : wb * gb1 = gb3 * wb := by
    apply Subtype.ext
    show wbM * gb1M = gb3M * wbM
    decide
  rw [h]
  group

theorem r1_inv (v : Fin 3 → ZMod 2) : (r1 v)⁻¹ = r1 v := by
  rw [inv_eq_iff_mul_eq_one, r1_mul]
  have : v + v = 0 := by
    funext i
    simp [CharTwo.add_self_eq_zero]
  rw [this, r1_zero]

theorem s3_inv (u : Fin 3 → ZMod 2) : (s3 u)⁻¹ = s3 u := by
  rw [inv_eq_iff_mul_eq_one, s3_mul]
  have : u + u = 0 := by
    funext i
    simp [CharTwo.add_self_eq_zero]
  rw [this, s3_zero]

theorem conj_r1 (v : Fin 3 → ZMod 2) : gb1 * r1 v * gb1⁻¹ = r1 (CmT *ᵥ v) := by
  have h : gb1 * r1 v = r1 (CmT *ᵥ v) * gb1 := by
    apply Subtype.ext
    show gb1M * r1M v = r1M (CmT *ᵥ v) * gb1M
    revert v
    decide
  rw [mul_inv_eq_iff_eq_mul]
  exact h

theorem conj_s3 (u : Fin 3 → ZMod 2) : gb3 * s3 u * gb3⁻¹ = s3 (Cm *ᵥ u) := by
  have h : gb3 * s3 u = s3 (Cm *ᵥ u) * gb3 := by
    apply Subtype.ext
    show gb3M * s3M u = s3M (Cm *ᵥ u) * gb3M
    revert u
    decide
  rw [mul_inv_eq_iff_eq_mul]
  exact h

theorem comm_r1 (v : Fin 3 → ZMod 2) : ⁅r1 v, gb1⁆ = r1 ((1 + CmT) *ᵥ v) := by
  have e : ⁅r1 v, gb1⁆ = r1 v * (gb1 * r1 v * gb1⁻¹) := by
    rw [commutatorElement_def, r1_inv]
    group
  rw [e, conj_r1, r1_mul, add_mulVec, one_mulVec]

theorem comm_s3 (u : Fin 3 → ZMod 2) : ⁅s3 u, gb3⁆ = s3 ((1 + Cm) *ᵥ u) := by
  have e : ⁅s3 u, gb3⁆ = s3 u * (gb3 * s3 u * gb3⁻¹) := by
    rw [commutatorElement_def, s3_inv]
    group
  rw [e, conj_s3, s3_mul, add_mulVec, one_mulVec]

theorem exists_one_add_CmT (w : Fin 3 → ZMod 2) : ∃ v, (1 + CmT) *ᵥ v = w := by
  revert w
  decide

theorem exists_one_add_Cm (w : Fin 3 → ZMod 2) : ∃ u, (1 + Cm) *ᵥ u = w := by
  revert w
  decide

theorem comm_Rrad1 : ⁅Rrad1, Subgroup.zpowers gb1⁆ = Rrad1 := by
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun r hr y hy => ?_
    have hyQ : y ∈ QI 4 {1} := (Subgroup.zpowers_le.2 gb1_mem) hy
    have h1 : y * r⁻¹ * y⁻¹ ∈ Rrad1 := Rrad1_normal hyQ (Rrad1.inv_mem hr)
    have e : ⁅r, y⁆ = r * (y * r⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Rrad1.mul_mem hr h1
  · intro x hx
    obtain ⟨w, rfl⟩ := mem_Rrad1_iff.1 hx
    obtain ⟨v, hv⟩ := exists_one_add_CmT w
    rw [← hv, ← comm_r1]
    exact Subgroup.commutator_mem_commutator (r1_mem_Rrad1 v) (Subgroup.mem_zpowers gb1)

theorem comm_Rrad3 : ⁅Rrad3, Subgroup.zpowers gb3⁆ = Rrad3 := by
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun r hr y hy => ?_
    have hyQ : y ∈ QI 4 {3} := (Subgroup.zpowers_le.2 gb3_mem) hy
    have h1 : y * r⁻¹ * y⁻¹ ∈ Rrad3 := Rrad3_normal hyQ (Rrad3.inv_mem hr)
    have e : ⁅r, y⁆ = r * (y * r⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Rrad3.mul_mem hr h1
  · intro x hx
    obtain ⟨w, rfl⟩ := mem_Rrad3_iff.1 hx
    obtain ⟨u, hu⟩ := exists_one_add_Cm w
    rw [← hu, ← comm_s3]
    exact Subgroup.commutator_mem_commutator (s3_mem_Rrad3 u) (Subgroup.mem_zpowers gb3)

end CFSG.Quasithin.SzC4

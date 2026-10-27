module

public import CFSG.Walter.ReeOrder.JT.AuxWeights
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13.NQTerm

open Matrix Module TensorProduct
open scoped MatrixGroups

section BaseChange

theorem finrank_range_baseChange {K E W : Type*} [Field K] [Field E] [Algebra K E]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (f : W →ₗ[K] W) :
    finrank E (LinearMap.range (f.baseChange E)) = finrank K (LinearMap.range f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.baseChange E)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have e := LinearMap.tensorKerEquiv E E f
  have h3 : f.baseChange E = AlgebraTensorModule.lTensor E E f := rfl
  have h4 : finrank E (LinearMap.ker (f.baseChange E)) = finrank K (LinearMap.ker f) := by
    rw [h3, ← e.finrank_eq, Module.finrank_baseChange]
  rw [Module.finrank_baseChange] at h1
  omega

end BaseChange

section Characters

theorem exists_isPrimitiveRoot_of_isAlgClosed {E : Type*} [Field E] [IsAlgClosed E] {n : ℕ}
    (hn : 0 < n) (hnE : (n : E) ≠ 0) : ∃ ζ : E, IsPrimitiveRoot ζ n := by
  have : NeZero (n : E) := ⟨hnE⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n E)
    (Polynomial.degree_cyclotomic_pos n E hn).ne'
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

end Characters

section Plane

open CFSG.Walter.JT

theorem weight_map_mul {E U Γ : Type*} [Field E] [AddCommGroup U] [Module E U] [Group Γ]
    {ρ : Representation E Γ U} {N : Subgroup Γ} {χ : N → E} (hχ : weightSpace ρ N χ ≠ ⊥)
    (a b : N) : χ (a * b) = χ a * χ b := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  rw [mem_weightSpace] at hw
  have h1 : ρ ((a * b : N) : Γ) w = (χ a * χ b) • w := by
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hw b, map_smul, hw a, smul_smul,
      mul_comm]
  rw [hw (a * b)] at h1
  exact smul_left_injective E hw0 h1

theorem weight_map_one {E U Γ : Type*} [Field E] [AddCommGroup U] [Module E U] [Group Γ]
    {ρ : Representation E Γ U} {N : Subgroup Γ} {χ : N → E} (hχ : weightSpace ρ N χ ≠ ⊥) :
    χ 1 = 1 := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  rw [mem_weightSpace] at hw
  have h1 := hw 1
  rw [Subgroup.coe_one, map_one, Module.End.one_apply] at h1
  exact (smul_left_injective E hw0 (h1.symm.trans (one_smul E w).symm))

variable {k : Type} [Field k]

end Plane

end CFSG.Quasithin.H13.NQTerm

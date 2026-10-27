
module

public import CFSG.Sporadic.Schreier.J4SFormBase

public import CFSG.Sporadic.Schreier.J4SCheck

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem jq_vecMul
    (g : J) (v : Fin 112 → ZMod 2) : jq (v ᵥ* φ g) = jq v := by
  have hg : g ∈ Subgroup.closure ({a, b} : Set J) := by rw [closure_ab]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction generalizing v with
  | mem g hg =>
    rcases hg with rfl | rfl
    · rw [← (rep_a matFacts).2.2.1]
      exact jq_vecMul_seed (defectOK_spec formDefect_check.1) v
    · rw [← (rep_b matFacts).2.2.1]
      exact jq_vecMul_seed (defectOK_spec formDefect_check.2) v
  | one => rw [map_one, Matrix.vecMul_one]
  | mul g h _ _ ihg ihh => rw [map_mul, ← Matrix.vecMul_vecMul, ihh, ihg]
  | inv g _ ih =>
    have e : v = (v ᵥ* φ g⁻¹) ᵥ* φ g := by
      rw [Matrix.vecMul_vecMul, ← map_mul, inv_mul_cancel, map_one, Matrix.vecMul_one]
    conv_rhs => rw [e]
    rw [ih]

theorem R3E_J4_invariant_nonsingular_binary_quadratic_form :
    (∀ v : Fin 112 → ZMod 2,
      jq v = (∑ i, ∑ j, if i < j then formF i j * v i * v j else 0) + ∑ i, v i) ∧
    (∀ u v : Fin 112 → ZMod 2, QuadraticMap.polar jq u v = u ⬝ᵥ (formF *ᵥ v)) ∧
    (QuadraticMap.polarBilin jq).Nondegenerate ∧
    ∀ g : J, ∀ v : Fin 112 → ZMod 2,
      jq (v ᵥ* ((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))) = jq v :=
  ⟨jq_eq_sum, polar_jq, jq_nondegenerate, fun g v => by rw [← φ_apply]; exact jq_vecMul g v⟩

end CFSG.Sporadic.J4Schreier


module

public import CFSG.Sporadic.Fi24.FaithfulBase
import all CFSG.Sporadic.Fi24.FaithfulBase

public import CFSG.Sporadic.Fi24.Orbit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

section Proj

variable {r : ℕ} (R : Matrix (Fin r) (Fin 781) (ZMod 3)) (F : Matrix (Fin 781) (Fin 781) (ZMod 3))
  (S : Matrix (Fin r) (Fin r) (ZMod 3))

end Proj

theorem exists_mul_eq {r : ℕ} (R : Matrix (Fin r) (Fin 781) (ZMod 3))
    (g : Matrix (Fin 781) (Fin 781) (ZMod 3))
    (h : ∀ i, g.mulVec (R i) ∈ Submodule.span (ZMod 3) (Set.range R)) :
    ∃ M : Matrix (Fin r) (Fin r) (ZMod 3), g * Rᵀ = Rᵀ * M := by
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).1 (h i)
  refine ⟨Matrix.of fun j i => c i j, ?_⟩
  ext a i
  have := congrFun (hc i) a
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [Finset.sum_apply] at this
  simp only [Pi.smul_apply, smul_eq_mul] at this
  calc ∑ j, g a j * Rᵀ j i = (g.mulVec (R i)) a := by
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    _ = ∑ x, c i x * R x a := this.symm
    _ = ∑ j, Rᵀ a j * (Matrix.of fun j i => c i j) j i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.transpose_apply, Matrix.of_apply, mul_comm]

theorem mulVec_mem_of_fix
    {g : J} {p : ℕ} (hg : g • pt p = pt p) (i : Fin 253) :
    (mat g).mulVec (matW 253 781 (form p).rows i) ∈
      Submodule.span (ZMod 3) (Set.range (matW 253 781 (form p).rows)) := by
  have hmem : matW 253 781 (form p).rows i ∈ (pt p).sp := by
    show matW 253 781 (form p).rows i ∈ rowSpan 253 (form p).rows
    unfold rowSpan; rw [matW_rows_eq]; exact Submodule.subset_span ⟨i, rfl⟩
  have : (mat g).mulVec (matW 253 781 (form p).rows i) ∈ (g • pt p).sp := by
    rw [smul_sp]
    have h1 := Submodule.mem_map_of_mem (f := Matrix.mulVecLin (mat g)) hmem
    rwa [Matrix.mulVecLin_apply] at h1
  rw [hg] at this
  change _ ∈ rowSpan 253 (form p).rows at this
  unfold rowSpan at this; rwa [matW_rows_eq] at this

theorem mat_inv_mul' (g : J) : mat g⁻¹ * mat g = 1 := mat_inv_mul g

end CFSG.Sporadic.Fi24

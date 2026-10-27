module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143L3Defs
import CFSG.RankThree.SubgroupLists.RationalElements
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open Matrix

variable {K : Type*} [Field K]

private def cubeProj (a : Matrix (Fin 3) (Fin 3) K) (c : K) : Matrix (Fin 3) (Fin 3) K :=
  a * a + c • a + c ^ 2 • 1

private theorem mul_cubeProj (a : Matrix (Fin 3) (Fin 3) K) (ha3 : a * a * a = 1) {c : K}
    (hc : c ^ 3 = 1) : a * cubeProj a c = c • cubeProj a c := by
  have e1 : a * cubeProj a c = a * a * a + c • (a * a) + c ^ 2 • a := by
    simp only [cubeProj, mul_add, mul_smul_comm, mul_one, mul_assoc]
  have e2 : c • cubeProj a c =
      c • (a * a) + c ^ 2 • a + c ^ 3 • (1 : Matrix (Fin 3) (Fin 3) K) := by
    unfold cubeProj
    module
  rw [e1, e2, ha3, hc]
  module

private theorem scalar_of_cubeProj_eq_zero (a : Matrix (Fin 3) (Fin 3) K) (ha3 : a * a * a = 1)
    (hdet : a.det = 1) (h3 : (3 : K) ≠ 0) {c : K} (hc : c ≠ 0) (h0 : cubeProj a c = 0) :
    ∃ s : K, a = Matrix.scalar (Fin 3) s := by
  have hadj : adjugate a = a * a := by
    have h1 : adjugate a * a = 1 := by rw [adjugate_mul, hdet, one_smul]
    calc adjugate a = adjugate a * (a * a * a) := by rw [ha3, mul_one]
      _ = (adjugate a * a) * a * a := by simp only [mul_assoc]
      _ = a * a := by rw [h1, one_mul]
  have hch := CFSG.RankThree.SubgroupLists.cayley_hamilton_three a
  rw [ha3, hdet, hadj, one_smul] at hch
  have hsq : a * a = -(c • a) - c ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K) := by
    unfold cubeProj at h0
    linear_combination (norm := module) h0
  have htr : (a * a).trace = -(c * a.trace) - 3 * c ^ 2 := by
    rw [hsq]
    simp [trace_smul, trace_one]
    ring
  rw [htr, hsq] at hch
  have key : (3 * c ^ 2) • a = (a.trace * c ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    linear_combination (norm := module) (-1 : K) • hch
  have hne : 3 * c ^ 2 ≠ 0 := mul_ne_zero h3 (pow_ne_zero 2 hc)
  refine ⟨(3 * c ^ 2)⁻¹ * (a.trace * c ^ 2), ?_⟩
  calc a = (3 * c ^ 2)⁻¹ • ((3 * c ^ 2) • a) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (3 * c ^ 2)⁻¹ • ((a.trace * c ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K)) := by rw [key]
    _ = ((3 * c ^ 2)⁻¹ * (a.trace * c ^ 2)) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [smul_smul]
    _ = Matrix.scalar (Fin 3) ((3 * c ^ 2)⁻¹ * (a.trace * c ^ 2)) := by
      rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

private theorem exists_eigenbasis_of_cube_inj (d : Fin 3 → K) (hd : Function.Injective d)
    (hd3 : ∀ j, d j ^ 3 = 1) (h3 : (3 : K) ≠ 0) (a : Matrix (Fin 3) (Fin 3) K)
    (ha3 : a ^ 3 = 1) (hdet : a.det = 1) (hns : ∀ c : K, a ≠ Matrix.scalar (Fin 3) c) :
    ∃ P : Matrix (Fin 3) (Fin 3) K, IsUnit P.det ∧ a * P = P * Matrix.diagonal d := by
  have ha3' : a * a * a = 1 := by rw [← pow_three', ha3]
  have hd0 : ∀ j, d j ≠ 0 := fun j h => by
    have := hd3 j
    rw [h] at this
    norm_num at this
  have hcol : ∀ j : Fin 3, ∃ i : Fin 3, (fun r => cubeProj a (d j) r i) ≠ 0 := by
    intro j
    by_contra hcon
    have hall : ∀ i, (fun r => cubeProj a (d j) r i) = 0 := fun i => by
      by_contra h
      exact hcon ⟨i, h⟩
    obtain ⟨s, hs⟩ := scalar_of_cubeProj_eq_zero a ha3' hdet h3 (hd0 j) (by
      ext r i
      simpa using congrFun (hall i) r)
    exact hns s hs
  choose ι hι using hcol
  have heig : ∀ j, a *ᵥ (fun r => cubeProj a (d j) r (ι j)) =
      d j • (fun r => cubeProj a (d j) r (ι j)) := by
    intro j
    funext s
    have h := congrFun (congrFun (mul_cubeProj a ha3' (hd3 j)) s) (ι j)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  have hli : LinearIndependent K (fun j : Fin 3 => fun r => cubeProj a (d j) r (ι j)) := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' a) d hd _ fun j => ?_
    refine ⟨?_, hι j⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact heig j
  refine ⟨Matrix.of fun r j => cubeProj a (d j) r (ι j), ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.linearIndependent_cols_iff_isUnit.1 hli
  · ext s j
    have h := congrFun (heig j) s
    rw [Matrix.mul_diagonal]
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [mul_comm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

theorem l143EigProp_holds : L143EigProp := by
  intro K _ ω hω3 hω1 a ha3 hdet hns
  have hω0 : ω ≠ 0 := fun h => by
    rw [h] at hω3
    norm_num at hω3
  have h3 : (3 : K) ≠ 0 := by
    intro h
    apply hω1
    have h' : (ω - 1) ^ 3 = 0 := by linear_combination hω3 + (ω - ω ^ 2) * h
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h')
  have hω2 : ω ^ 2 ≠ 1 := fun h => by
    apply hω1
    calc ω = ω * ω ^ 2 := by rw [h, mul_one]
      _ = 1 := by rw [← hω3]; ring
  have hω21 : ω ^ 2 ≠ ω := fun h => by
    have : ω * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact hω0 h0
    · exact hω1 (sub_eq_zero.1 h0)
  refine exists_eigenbasis_of_cube_inj ![1, ω, ω ^ 2] ?_ ?_ h3 a ha3 hdet hns
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact (hω1 (by simpa using hij)).elim
      | exact (hω1 (by simpa using hij.symm)).elim
      | exact (hω2 (by simpa using hij)).elim
      | exact (hω2 (by simpa using hij.symm)).elim
      | exact (hω21 (by simpa using hij)).elim
      | exact (hω21 (by simpa using hij.symm)).elim
  · intro j
    fin_cases j
    · simp
    · simpa using hω3
    · calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hω3]; norm_num

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143

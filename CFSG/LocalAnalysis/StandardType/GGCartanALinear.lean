module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType

section CartanA

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {r : ℕ}

theorem cartanA_eq_zero_of_mulVec (hpr : ¬ p ∣ r + 1) {c : Fin r → ZMod p}
    (hc : ∀ i, ∑ j, (CartanMatrix.A r i j : ZMod p) * c j = 0) : c = 0 := by
  have hdet : ((CartanMatrix.A r).map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
    change ((CartanMatrix.A r).map (fun x : ℤ => (x : ZMod p))).det ≠ 0
    rw [← Int.cast_det (R := ZMod p) (CartanMatrix.A r), CartanMatrix.A_det]
    intro h
    apply hpr
    have h' : (p : ℤ) ∣ (r : ℤ) + 1 := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact_mod_cast h'
  refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
  funext i
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hc i

theorem cartanA_eq_zero_of_mem_span (hpr : ¬ p ∣ r + 1) {h : Fin r → V}
    {α : Fin r → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod p)) {v : V}
    (hv : v ∈ Submodule.span (ZMod p) (Set.range h)) (hα : ∀ i, α i v = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hv
  have hc : c = 0 := cartanA_eq_zero_of_mulVec hpr fun i => by
    rw [← hα i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hpair, mul_comm]
  simp [hc]

theorem cartanA_linearIndependent (hpr : ¬ p ∣ r + 1) {h : Fin r → V}
    {α : Fin r → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod p)) :
    LinearIndependent (ZMod p) h := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : c = 0 := cartanA_eq_zero_of_mulVec hpr fun i => by
    have hi := congrArg (α i) hc
    rw [map_sum, map_zero] at hi
    rw [← hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hpair, mul_comm]
  intro i
  rw [h0, Pi.zero_apply]

end CartanA

end CFSG.StandardType

end

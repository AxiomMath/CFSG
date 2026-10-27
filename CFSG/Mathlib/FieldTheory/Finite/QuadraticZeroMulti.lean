module

import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.LinearAlgebra.BilinearForm.Hom

public section

namespace CFSG.FiniteField

open MvPolynomial

theorem exists_ne_zero_forall_eq_zero_of_quadraticForm {K V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ}
    (Q : Fin r → QuadraticForm K V) (h : 2 * r < Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, Q i v = 0 := by
  classical
  let := Fintype.ofFinite K
  let b : Module.Basis (Fin (Module.finrank K V)) K V := Module.finBasis K V
  let B : Fin r → LinearMap.BilinForm K V := fun i => (Q i).toBilin b
  let P : Fin r → MvPolynomial (Fin (Module.finrank K V)) K := fun i =>
    ∑ j, ∑ k, X j * (X k * C (B i (b j) (b k)))
  have hPdeg : ∀ i, (P i).totalDegree ≤ 2 := by
    intro i
    refine totalDegree_finsetSum_le fun j _ => totalDegree_finsetSum_le fun k _ => ?_
    calc (X j * (X k * C (B i (b j) (b k)))).totalDegree
        ≤ (X j).totalDegree + (X k * C (B i (b j) (b k))).totalDegree :=
          totalDegree_mul _ _
      _ ≤ (X j).totalDegree +
          ((X k).totalDegree + (C (B i (b j) (b k))).totalDegree) := by
          gcongr
          exact totalDegree_mul _ _
      _ = 2 := by simp
  have hdeg : (∑ i : Fin r, (P i).totalDegree) < Fintype.card (Fin (Module.finrank K V)) := by
    have hsum : (∑ i : Fin r, (P i).totalDegree) ≤ 2 * r := by
      calc (∑ i : Fin r, (P i).totalDegree) ≤ ∑ _i : Fin r, 2 :=
            Finset.sum_le_sum fun i _ => hPdeg i
        _ = 2 * r := by simp [mul_comm]
    simpa [Fintype.card_fin] using lt_of_le_of_lt hsum h
  have heval : ∀ (x : Fin (Module.finrank K V) → K) (i : Fin r),
      eval x (P i) = Q i (b.equivFun.symm x) := by
    intro x i
    rw [b.equivFun_symm_apply, ← QuadraticMap.toQuadraticMap_toBilin (Q i) b,
      LinearMap.BilinMap.toQuadraticMap_apply]
    have hB : B i (∑ j, x j • b j) (∑ k, x k • b k)
        = ∑ j, ∑ k, x j * (x k * B i (b j) (b k)) := by
      rw [LinearMap.BilinForm.sum_left]
      simp_rw [LinearMap.BilinForm.sum_right]
      simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hB]
    simp only [P, map_sum, map_mul, eval_C, eval_X]
  have hdvd : ringChar K ∣
      Nat.card {x : Fin (Module.finrank K V) → K // ∀ i, eval x (P i) = 0} := by
    simpa only [← Nat.card_eq_fintype_card] using
      char_dvd_card_solutions_of_fintype_sum_lt (K := K)
        (σ := Fin (Module.finrank K V)) (ringChar K) (f := P) hdeg
  have hmem0 : ∀ i, eval (0 : Fin (Module.finrank K V) → K) (P i) = 0 := by
    intro i
    rw [heval 0 i]
    simp
  let z : {x : Fin (Module.finrank K V) → K // ∀ i, eval x (P i) = 0} := ⟨0, hmem0⟩
  have hpos : 0 < Nat.card {x : Fin (Module.finrank K V) → K //
      ∀ i, eval x (P i) = 0} :=
    Nat.card_pos_iff.mpr ⟨⟨z⟩, inferInstance⟩
  have hgt : 1 < Nat.card {x : Fin (Module.finrank K V) → K //
      ∀ i, eval x (P i) = 0} := by
    have hp2 : 2 ≤ ringChar K := (CharP.char_is_prime K (ringChar K)).two_le
    have hle := Nat.le_of_dvd hpos hdvd
    omega
  have : Nontrivial {x : Fin (Module.finrank K V) → K // ∀ i, eval x (P i) = 0} :=
    Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨y, hy⟩ := exists_ne z
  refine ⟨b.equivFun.symm y.1, ?_, fun i => ?_⟩
  · intro hv
    apply hy
    apply Subtype.ext
    apply b.equivFun.symm.injective
    rw [hv]
    simp [z]
  · rw [← heval y.1 i]
    exact y.2 i

end CFSG.FiniteField

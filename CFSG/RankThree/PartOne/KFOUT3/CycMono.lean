module

public import CFSG.RankThree.PartOne.KFOUT3.CycKrylov
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Matrix

variable {K : Type} [Field K]

theorem perm_three_cycle_facts : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 →
    σ 0 ≠ 0 ∧ σ (σ 0) ≠ 0 ∧ σ (σ 0) ≠ σ 0 := by
  decide

theorem mulVec_single_monomial {σ : Equiv.Perm (Fin 3)} {m : Matrix (Fin 3) (Fin 3) K}
    (hmono : ∀ i k, k ≠ σ i → m k i = 0) (i : Fin 3) :
    m *ᵥ (Pi.single i (1 : K)) = fun k => if k = σ i then m (σ i) i else 0 := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hk : k = σ i
  · subst hk
    simp
  · simp [hk, hmono i k hk]

theorem isUnit_det_krylov_of_monomial {σ : Equiv.Perm (Fin 3)} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {m : Matrix (Fin 3) (Fin 3) K} (hmono : ∀ i k, k ≠ σ i → m k i = 0) (hdet : IsUnit m.det) :
    IsUnit (krylov m (Pi.single 0 (1 : K))).det := by
  obtain ⟨h1, h2, h3⟩ := perm_three_cycle_facts σ hσ3 hσ1
  have hμ : ∀ i, m (σ i) i ≠ 0 := by
    intro i h0
    have : m.det = 0 := Matrix.det_eq_zero_of_column_eq_zero i (fun j => by
      by_cases hj : j = σ i
      · rw [hj]; exact h0
      · exact hmono i j hj)
    exact hdet.ne_zero this
  rw [isUnit_iff_ne_zero]
  intro hd
  obtain ⟨a, ha, hka⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  apply ha
  have hme0 : m *ᵥ (Pi.single 0 (1 : K)) = fun k => if k = σ 0 then m (σ 0) 0 else 0 :=
    mulVec_single_monomial hmono 0
  have hme1 : m *ᵥ (m *ᵥ (Pi.single 0 (1 : K))) =
      fun k => if k = σ (σ 0) then m (σ 0) 0 * m (σ (σ 0)) (σ 0) else 0 := by
    have : (fun k => if k = σ 0 then m (σ 0) 0 else 0) = m (σ 0) 0 • Pi.single (σ 0) (1 : K) := by
      funext k
      simp [Pi.single_apply]
    rw [hme0, this, Matrix.mulVec_smul, mulVec_single_monomial hmono (σ 0)]
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hk := krylov_mulVec m (Pi.single 0 (1 : K)) a
  rw [hka, hme1, hme0] at hk
  have e0 := congrFun hk 0
  have eb := congrFun hk (σ 0)
  have ec := congrFun hk (σ (σ 0))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.zero_apply] at e0 eb ec
  have a0 : a 0 = 0 := by
    simpa [Ne.symm h1, Ne.symm h2] using e0.symm
  have a1 : a 1 = 0 := by
    have : a 1 * m (σ 0) 0 = 0 := by simpa [h1, h3.symm, Ne.symm h1] using eb.symm
    exact (mul_eq_zero.1 this).resolve_right (hμ 0)
  have a2 : a 2 = 0 := by
    have : a 2 * (m (σ 0) 0 * m (σ (σ 0)) (σ 0)) = 0 := by
      simpa [h2, h3, Ne.symm h2] using ec.symm
    exact (mul_eq_zero.1 this).resolve_right (mul_ne_zero (hμ 0) (hμ (σ 0)))
  funext i
  fin_cases i <;> simp [a0, a1, a2]

end CFSG.RankThree.PartOne.KFOUT3

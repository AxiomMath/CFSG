module

public import Mathlib.FieldTheory.ChevalleyWarning

public section

namespace CFSG.RankThree.PartOne.D4RC

open MvPolynomial

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

noncomputable def rcwPush (π : L →ₗ[F] F) (P : MvPolynomial (Fin 6) L) :
    MvPolynomial (Fin 6) F :=
  ∑ m ∈ P.support, monomial m (π (P.coeff m))

theorem rcwPush_eval (π : L →ₗ[F] F) (P : MvPolynomial (Fin 6) L) (x : Fin 6 → F) :
    eval x (rcwPush π P) = π (eval (algebraMap F L ∘ x) P) := by
  conv_rhs => rw [P.as_sum]
  simp only [rcwPush, map_sum, eval_monomial]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (m.prod fun n k => (algebraMap F L ∘ x) n ^ k) =
      algebraMap F L (m.prod fun n k => x n ^ k) := by
    rw [map_finsuppProd]
    simp only [Function.comp_apply, map_pow]
  rw [e, mul_comm (P.coeff m), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem rcwPush_totalDegree_le (π : L →ₗ[F] F) (P : MvPolynomial (Fin 6) L) :
    (rcwPush π P).totalDegree ≤ P.totalDegree := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hm)

theorem rcw_exists_zero [Fintype F] [DecidableEq F] [CharP F 2]
    {N : MvPolynomial (Fin 6) F} {P : MvPolynomial (Fin 6) L} (hN : N.totalDegree ≤ 2)
    (hP : P.totalDegree ≤ 2) (hN0 : eval 0 N = 0) (hP0 : eval 0 P = 0)
    (hrat : ∀ x : Fin 6 → F, eval x N = 0 →
      ∃ a : F, eval (algebraMap F L ∘ x) P = algebraMap F L a) :
    ∃ x : Fin 6 → F, x ≠ 0 ∧ eval x N = 0 ∧ eval (algebraMap F L ∘ x) P = 0 := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F L)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap F L).injective)
  have hπa : ∀ a : F, π (algebraMap F L a) = a := fun a => LinearMap.congr_fun hπ a
  have hP' : (rcwPush π P).totalDegree ≤ 2 := (rcwPush_totalDegree_le π P).trans hP
  have hcw := char_dvd_card_solutions_of_add_lt (p := 2) (f₁ := N) (f₂ := rcwPush π P)
    (by simp only [Fintype.card_fin]; omega)
  have h0 : eval 0 (rcwPush π P) = 0 := by
    rw [rcwPush_eval]
    have e : (algebraMap F L ∘ (0 : Fin 6 → F)) = 0 := by
      funext i
      simp
    rw [e, hP0, map_zero]
  set z : {x : Fin 6 → F // eval x N = 0 ∧ eval x (rcwPush π P) = 0} := ⟨0, hN0, h0⟩
  have hpos : 0 < Fintype.card {x : Fin 6 → F // eval x N = 0 ∧ eval x (rcwPush π P) = 0} :=
    Fintype.card_pos_iff.2 ⟨z⟩
  have h2 : 1 < Fintype.card {x : Fin 6 → F // eval x N = 0 ∧ eval x (rcwPush π P) = 0} := by
    obtain ⟨k, hk⟩ := hcw
    omega
  obtain ⟨⟨x, hxN, hxP⟩, hx0⟩ := Fintype.exists_ne_of_one_lt_card h2 z
  refine ⟨x, fun e => hx0 (Subtype.ext e), hxN, ?_⟩
  obtain ⟨a, ha⟩ := hrat x hxN
  rw [rcwPush_eval, ha, hπa] at hxP
  rw [ha, hxP, map_zero]

end CFSG.RankThree.PartOne.D4RC

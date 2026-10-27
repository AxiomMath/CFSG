module

public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix
open CFSG.Assembly.RankThreeEven (projSL)

section SL2

variable {F : Type} [Field F] [CharP F 2]

theorem sq_eq_one_add_trace_smul (x : Matrix (Fin 2) (Fin 2) F) (hdet : x.det = 1) :
    x ^ 2 = 1 + (x 0 0 + x 1 1) • x := by
  have hd : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := by rw [← det_fin_two]; exact hdet
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (-1 : F) * hd - h2

theorem exists_matrix_inv_conj (a b c d : F) (ht : a + d ≠ 0) :
    ∃ J : Matrix (Fin 2) (Fin 2) F, J.det = 1 ∧ J * J = 1 ∧
      J * !![a, b; c, d] = !![d, -b; -c, a] * J := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hneg : ∀ x : F, -x = x := fun x => by linear_combination (-x) * h2
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · refine ⟨!![0, 1; 1, 0], ?_, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]; linear_combination -h2
      · rw [Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      · rw [Matrix.mul_fin_two, Matrix.mul_fin_two, hb, hc]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
    · refine ⟨!![1, 0; (a + d) / b, 1], ?_, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]; ring
      · rw [Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
        linear_combination ((a + d) / b) * h2
      · rw [Matrix.mul_fin_two, Matrix.mul_fin_two, hc]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hneg] <;> field_simp <;> ring_nf <;>
          simp only [h2, mul_zero, add_zero, zero_add]
  · refine ⟨!![1, (a + d) / c; 0, 1], ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]; ring
    · rw [Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      linear_combination ((a + d) / c) * h2
    · rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hneg] <;> field_simp <;> ring_nf <;>
        simp only [h2, mul_zero, zero_add]

@[expose] def sl2OrderThree : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 1], by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    rw [Matrix.det_fin_two_of]; linear_combination -h2⟩

theorem coe_sl2OrderThree :
    ((sl2OrderThree : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 1] := rfl

theorem orderOf_sl2OrderThree : orderOf (sl2OrderThree : SpecialLinearGroup (Fin 2) F) = 3 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  refine orderOf_eq_prime (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_) fun h => ?_
  · rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2OrderThree, Matrix.SpecialLinearGroup.coe_one,
      pow_succ, pow_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2
  · have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [coe_sl2OrderThree] at this

theorem eq_one_of_mem_center_sl2 {x : SpecialLinearGroup (Fin 2) F}
    (hx : x ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : x = 1 := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have h : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [← hrx, hr1, Matrix.SpecialLinearGroup.coe_one]
  simp

theorem exists_inv_conj_sl2 {x : SpecialLinearGroup (Fin 2) F} (hx : orderOf x = 3) :
    ∃ j : SpecialLinearGroup (Fin 2) F, j * j = 1 ∧ j * x = x⁻¹ * j := by
  have ht : (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro ht
    have hsq := sq_eq_one_add_trace_smul (x : Matrix (Fin 2) (Fin 2) F) x.2
    rw [ht, zero_smul, add_zero] at hsq
    have hx2 : x ^ 2 = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_pow, hsq, Matrix.SpecialLinearGroup.coe_one]
    have := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at this
    norm_num at this
  obtain ⟨J, hJdet, hJJ, hJx⟩ := exists_matrix_inv_conj ((x : Matrix (Fin 2) (Fin 2) F) 0 0)
    ((x : Matrix (Fin 2) (Fin 2) F) 0 1) ((x : Matrix (Fin 2) (Fin 2) F) 1 0)
    ((x : Matrix (Fin 2) (Fin 2) F) 1 1) ht
  refine ⟨(⟨J, hJdet⟩ : SpecialLinearGroup (Fin 2) F),
    Matrix.SpecialLinearGroup.ext _ _ fun i k => ?_,
    Matrix.SpecialLinearGroup.ext _ _ fun i k => ?_⟩
  · change (J * J) i k = (1 : Matrix (Fin 2) (Fin 2) F) i k
    rw [hJJ]
  · change (J * (x : Matrix (Fin 2) (Fin 2) F)) i k =
      (((x⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * J) i k
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    have h := congrFun (congrFun hJx i) k
    rw [← Matrix.eta_fin_two (x : Matrix (Fin 2) (Fin 2) F)] at h
    exact h

end SL2

section L2

@[expose] noncomputable def projSLTwoEquivSL (F : Type) [Field F] [CharP F 2] :
    projSL 2 F ≃* SpecialLinearGroup (Fin 2) F :=
  (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL F).trans
    ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      2 F).trans (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL F))

variable {X : Type*} [Group X] {n : ℕ}

theorem three_dvd_card_of_mulEquiv_projSL [Finite X] (e : X ≃* projSL 2 (GaloisField 2 n)) :
    3 ∣ Nat.card X := by
  let e' := e.trans (projSLTwoEquivSL (GaloisField 2 n))
  have h := orderOf_dvd_natCard (e'.symm sl2OrderThree)
  rwa [MulEquiv.orderOf_eq, orderOf_sl2OrderThree] at h

theorem eq_one_of_forall_commute_of_mulEquiv_projSL (e : X ≃* projSL 2 (GaloisField 2 n))
    {y : X} (hy : ∀ x : X, x * y = y * x) : y = 1 := by
  let e' := e.trans (projSLTwoEquivSL (GaloisField 2 n))
  have hc : e' y ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg e' (hy (e'.symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  have := eq_one_of_mem_center_sl2 hc
  rwa [MulEquiv.map_eq_one_iff] at this

theorem exists_inv_conj_of_mulEquiv_projSL (e : X ≃* projSL 2 (GaloisField 2 n)) {z : X}
    (hz : orderOf z = 3) : ∃ j : X, j * j = 1 ∧ j * z * j⁻¹ = z⁻¹ := by
  let e' := e.trans (projSLTwoEquivSL (GaloisField 2 n))
  have hz' : orderOf (e' z) = 3 := by rw [MulEquiv.orderOf_eq]; exact hz
  obtain ⟨j, hjj, hjz⟩ := exists_inv_conj_sl2 hz'
  refine ⟨e'.symm j, ?_, ?_⟩
  · rw [← map_mul, hjj, map_one]
  · rw [mul_inv_eq_iff_eq_mul]
    apply e'.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hjz]

end L2

end CFSG.RankThree.PartTwo.Sec21

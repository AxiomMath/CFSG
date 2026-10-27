module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier
import CFSG.RankThree.PartTwo.KFacts.L34Sections

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8ModelProof

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL)
open Matrix

@[expose] def sixMat (K : Type*) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

variable {K : Type*} [Field K] [CharP K 2]

theorem det_sixMat : (sixMat K).det = 1 := by
  rw [sixMat, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  exact CharTwo.neg_eq (1 : K)

theorem sixMat_sq : sixMat K * sixMat K = !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sixMat, Matrix.mul_apply, Fin.sum_univ_four, h2]

theorem sixMat_cube : sixMat K * sixMat K * sixMat K =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1] := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [sixMat_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sixMat, Matrix.mul_apply, Fin.sum_univ_four, h2]

theorem sixMat_cube_sq : (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1] :
    Matrix (Fin 4) (Fin 4) K) * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1] = 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, h2]

@[expose] noncomputable def sixElt (K : Type*) [Field K] [CharP K 2] :
    SpecialLinearGroup (Fin 4) K :=
  ⟨sixMat K, det_sixMat⟩

theorem sixElt_sq_apply : ((sixElt K ^ 2 : SpecialLinearGroup (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K) 0 1 = 1 := by
  change (sixMat K ^ 2) 0 1 = 1
  rw [pow_two, sixMat_sq]
  simp

theorem sixElt_cube_apply : ((sixElt K ^ 3 : SpecialLinearGroup (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K) 2 3 = 1 := by
  change (sixMat K ^ 3) 2 3 = 1
  rw [pow_three, ← mul_assoc, sixMat_cube]
  simp

theorem sixElt_pow_six : sixElt K ^ 6 = 1 := by
  apply Subtype.ext
  change sixMat K ^ 6 = 1
  rw [show (6 : ℕ) = 3 * 2 by rfl, pow_mul, pow_three, ← mul_assoc, sixMat_cube, pow_two,
    sixMat_cube_sq]

omit [CharP K 2] in
theorem not_mem_scalars_of_apply {n : ℕ} {A : SpecialLinearGroup (Fin n) K} {i j : Fin n}
    (hij : i ≠ j) (h : (A : Matrix (Fin n) (Fin n) K) i j ≠ 0) : A ∉ scalars n K := by
  rintro ⟨c, -, hc⟩
  rw [hc, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at h
  exact h rfl

theorem orderOf_eq_six {G : Type*} [Group G] {x : G} (h6 : x ^ 6 = 1) (h2 : x ^ 2 ≠ 1)
    (h3 : x ^ 3 ≠ 1) : orderOf x = 6 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h6 fun p hp hpd => ?_
  have hp6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpd
  interval_cases p
  · norm_num at hp
  · norm_num at hp
  · simpa using h3
  · simpa using h2
  · norm_num at hp
  · norm_num at hpd
  · norm_num at hp

theorem exists_orderOf_six (K : Type*) [Field K] [CharP K 2] :
    ∃ g : SpecialLinearGroup (Fin 4) K, orderOf g = 6 ∧ orderOf (proj 4 K g) = 6 := by
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  have hs2 : sixElt K ^ 2 ∉ scalars 4 K :=
    not_mem_scalars_of_apply (i := 0) (j := 1) (by decide) (by rw [sixElt_sq_apply]; exact h1)
  have hs3 : sixElt K ^ 3 ∉ scalars 4 K :=
    not_mem_scalars_of_apply (i := 2) (j := 3) (by decide) (by rw [sixElt_cube_apply]; exact h1)
  refine ⟨sixElt K, orderOf_eq_six sixElt_pow_six (fun h => hs2 (h ▸ Subgroup.one_mem _))
    (fun h => hs3 (h ▸ Subgroup.one_mem _)), orderOf_eq_six ?_ ?_ ?_⟩
  · rw [← map_pow, sixElt_pow_six, map_one]
  · rw [← map_pow, Ne, proj_eq_one_iff]
    exact hs2
  · rw [← map_pow, Ne, proj_eq_one_iff]
    exact hs3

theorem false_of_orderOf_six {X : Type} [Group X]
    (eX : X ≃* projSL 3 (GaloisField 2 2)) {x : X} (hx : orderOf x = 6) : False := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  have hst : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 2 :=
    ⟨hadm, GaloisField 2 2, inferInstance, inferInstance,
      by rw [KFacts.L34.card_galoisField_two_two]; norm_num,
      ⟨eX.trans (KFacts.KS44.projSLEquivStatedProj _)⟩⟩
  obtain ⟨-, hcent, -⟩ :=
    CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated.{0} X hst
  have ht : orderOf (x ^ 3) = 2 := by
    rw [orderOf_pow' x (by norm_num), hx]
    decide
  have hmem : x ∈ Subgroup.centralizer ({x ^ 3} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.refl x).pow_right 3).eq
  have hdvd : orderOf (⟨x, hmem⟩ : Subgroup.centralizer ({x ^ 3} : Set X)) ∣
      Nat.card (Subgroup.centralizer ({x ^ 3} : Set X)) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hx, hcent _ ht] at hdvd
  norm_num at hdvd

theorem false_of_mulEquiv_projectiveSL_four {X : Type} [Group X]
    (eX : X ≃* projSL 3 (GaloisField 2 2)) {K : Type*} [Field K] [CharP K 2]
    (e : X ≃* projectiveSL 4 K) : False := by
  obtain ⟨g, -, hg⟩ := exists_orderOf_six K
  exact false_of_orderOf_six eX (x := e.symm (proj 4 K g)) (by rw [MulEquiv.orderOf_eq]; exact hg)

theorem false_of_mulEquiv_SL_four {X : Type} [Group X]
    (eX : X ≃* projSL 3 (GaloisField 2 2)) {K : Type*} [Field K] [CharP K 2]
    (e : X ≃* SpecialLinearGroup (Fin 4) K) : False := by
  obtain ⟨g, hg, -⟩ := exists_orderOf_six K
  exact false_of_orderOf_six eX (x := e.symm g) (by rw [MulEquiv.orderOf_eq]; exact hg)

end CFSG.RankThree.PartTwo.Sec8.Item8ModelProof

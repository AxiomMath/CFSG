module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldArithmetic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open scoped MatrixGroups

theorem mul_ne_mul_of_isPSL_three_two_two {X : Type} [Group X] (h : IsPSL 3 2 2 X) {a t : X}
    (ha : orderOf a = 3) (ht : orderOf t = 2) : a * t ≠ t * a := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  let ε : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  intro hat
  apply CFSG.RankThree.PartTwo.KFacts.L34.mul_ne_mul_of_orderOf hK4 (a := ε a) (t := ε t)
    (by rw [MulEquiv.orderOf_eq]; exact ha)
    (by rw [MulEquiv.orderOf_eq]; exact ht)
  rw [← map_mul, hat, map_mul]

theorem exists_commute_of_isPSL_four_two_one {Y : Type} [Group Y] (h : IsPSL 4 2 1 Y) :
    ∃ a t : Y, orderOf a = 3 ∧ orderOf t = 2 ∧ a * t = t * a := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have : CharP K 2 := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card hK
  have := Fintype.ofFinite K
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hone : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by
    have h1 := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [← Nat.card_eq_fintype_card, hK2, show 2 - 1 = 1 from rfl, pow_one] at h1
  have hdet : ∀ M N : Matrix (Fin 4) (Fin 4) K, M * N = 1 → M.det = 1 := fun M N hMN => by
    apply hone
    intro h0
    have h1 := congrArg Matrix.det hMN
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  let A : Matrix (Fin 4) (Fin 4) K := !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  let B : Matrix (Fin 4) (Fin 4) K := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]
  have hA3 : A * (A * A) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_four, h2]
  have hB2 : B * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, Matrix.mul_apply, Fin.sum_univ_four, h2]
  have hAB : A * B = B * A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_four]
  let a : SL(4, K) := ⟨A, hdet A (A * A) hA3⟩
  let t : SL(4, K) := ⟨B, hdet B B hB2⟩
  have ha3 : a ^ 3 = 1 := by
    rw [pow_three]
    exact Subtype.ext hA3
  have ht2 : t ^ 2 = 1 := by
    rw [sq]
    exact Subtype.ext hB2
  have hat : a * t = t * a := Subtype.ext hAB
  have hnc : ∀ (g : SL(4, K)) (i j : Fin 4), i ≠ j → (g : Matrix (Fin 4) (Fin 4) K) i j ≠ 0 →
      g ∉ Subgroup.center SL(4, K) := by
    intro g i j hij hg hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    apply hg
    rw [← hr]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
  set π := QuotientGroup.mk' (Subgroup.center SL(4, K)) with hπ
  have h01 : (a : Matrix (Fin 4) (Fin 4) K) 0 1 ≠ 0 := by simp [a, A]
  have h23 : (t : Matrix (Fin 4) (Fin 4) K) 2 3 ≠ 0 := by simp [t, B]
  have hπa : orderOf (π a) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime (by rw [← map_pow, ha3, map_one]) fun h1 => ?_
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hnc a 0 1 (by decide) h01 h1
  have hπt : orderOf (π t) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) fun h1 => ?_
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hnc t 2 3 (by decide) h23 h1
  let ε : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm
  refine ⟨ε.symm (π a), ε.symm (π t), ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hπa
  · rw [MulEquiv.orderOf_eq]
    exact hπt
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hat]

theorem not_isPSL_four_two_one_of_isPSL_three_two_two {X : Type} [Group X] (h : IsPSL 3 2 2 X) :
    ¬ IsPSL 4 2 1 X := fun h' => by
  obtain ⟨a, t, ha, ht, hat⟩ := exists_commute_of_isPSL_four_two_one h'
  exact mul_ne_mul_of_isPSL_three_two_two h ha ht hat

theorem not_nonempty_mulEquiv_psl_three_four {X Y : Type} [Group X] [Group Y] (hX : IsPSL 3 2 2 X)
    (hY : IsPSL 4 2 1 Y) : ¬ Nonempty (X ≃* Y) := fun ⟨φ⟩ => by
  obtain ⟨a, t, ha, ht, hat⟩ := exists_commute_of_isPSL_four_two_one hY
  apply mul_ne_mul_of_isPSL_three_two_two hX (a := φ.symm a) (t := φ.symm t)
    (by rw [MulEquiv.orderOf_eq]; exact ha)
    (by rw [MulEquiv.orderOf_eq]; exact ht)
  rw [← map_mul, hat, map_mul]

end CFSG.Quasithin.Vol2.Ch11.SecB

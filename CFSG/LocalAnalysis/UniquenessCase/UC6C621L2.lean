module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C621Inv
public import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup Matrix
open scoped MatrixGroups

theorem psl_mk_eq_iff {n : Type} [Fintype n] [DecidableEq n] {R : Type} [CommRing R]
    (g h : SpecialLinearGroup n R) :
    (QuotientGroup.mk g : ProjectiveSpecialLinearGroup n R) = QuotientGroup.mk h ↔
      ∃ u : Rˣ, (h : Matrix n n R) = (u : R) • (g : Matrix n n R) := by
  rw [← ProjectiveSpecialLinearGroup.toPGL_injective.eq_iff]
  simp only [ProjectiveSpecialLinearGroup.toPGL_mk]
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  have key : ∀ (u : Rˣ), ((SpecialLinearGroup.toGL g : GL n R) : Matrix n n R) *
      (scalar n) (u : R) = (u : R) • (g : Matrix n n R) := fun u => by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    rfl
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have := congrArg (fun A : GL n R => (A : Matrix n n R)) hu
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [key u] at this
    exact this.symm
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply Units.ext
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar]
    rw [key u]
    exact hu.symm

section SL2

variable {K : Type} [Field K]

@[expose] def sl2U (b : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def sl2D (a : K) (ha : a ≠ 0) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, ha]⟩

theorem sl2U_add (b c : K) : sl2U b * sl2U c = sl2U (b + c) := by
  apply Subtype.ext
  change (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, c; 0, 1] = !![1, b + c; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sl2U_zero : sl2U (0 : K) = 1 := by
  apply Subtype.ext
  change (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2D_mul_sl2U (a : K) (ha : a ≠ 0) (b : K) :
    sl2D a ha * sl2U b = sl2U (a ^ 2 * b) * sl2D a ha := by
  apply Subtype.ext
  change (!![a, 0; 0, a⁻¹] : Matrix (Fin 2) (Fin 2) K) * !![1, b; 0, 1] =
    !![1, a ^ 2 * b; 0, 1] * !![a, 0; 0, a⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem sl2D_sq_mul_sl2U (a : K) (ha : a ≠ 0) (b : K) :
    sl2D a ha * sl2D a ha * sl2U b = sl2U (a ^ 4 * b) * (sl2D a ha * sl2D a ha) := by
  rw [mul_assoc, sl2D_mul_sl2U, ← mul_assoc, sl2D_mul_sl2U, mul_assoc]
  congr 2
  ring

theorem mk_sl2U_injective {b c : K}
    (h : (QuotientGroup.mk (sl2U b) : PSL(2, K)) = QuotientGroup.mk (sl2U c)) : b = c := by
  obtain ⟨u, hu⟩ := (psl_mk_eq_iff _ _).1 h
  have h00 := congrFun (congrFun hu 0) 0
  have h01 := congrFun (congrFun hu 0) 1
  simp [sl2U] at h00 h01
  rw [h01, ← h00]
  simp

theorem sl2U_pow_three (h3 : (3 : K) = 0) (b : K) : sl2U b ^ 3 = 1 := by
  rw [pow_three, sl2U_add, sl2U_add, show b + (b + b) = 0 by
    calc b + (b + b) = 3 * b := by ring
      _ = 0 := by rw [h3, zero_mul], sl2U_zero]

theorem charP_three_of_card_nine [Finite K] (hK : Nat.card K = 9) : CharP K 3 := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact charP_of_card_eq_prime_pow (p := 3) (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

theorem exists_pow_four_eq_neg_one [Finite K] (hK : Nat.card K = 9) : ∃ a : K, a ^ 4 = -1 := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgo : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  refine ⟨(g : K), ?_⟩
  have hne : g ^ 4 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hgo] at this
    omega
  have hsq : (g ^ 4) ^ 2 = 1 := by
    rw [← pow_mul, show 4 * 2 = orderOf g by rw [hgo], pow_orderOf_eq_one]
  have h2 : ((g ^ 4 : Kˣ) : K) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  rcases sq_eq_one_iff.mp h2 with h | h
  · exact absurd (Units.ext h) hne
  · rw [← Units.val_pow_eq_pow_val]
    exact h

theorem card_psl_two_of_card_nine [Finite K] (hK : Nat.card K = 9) :
    Nat.card PSL(2, K) = 9 * 40 := by
  have h1 := Nat.card_congr
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).toEquiv
  rw [h1, CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hK]; decide), hK]
  norm_num

theorem invNormalizer_psl_two_of_card_nine [Finite K] (hK : Nat.card K = 9) :
    InvNormalizer 3 PSL(2, K) := by
  haveI := charP_three_of_card_nine hK
  obtain ⟨a, ha4⟩ := exists_pow_four_eq_neg_one hK
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hm1 : (-1 : K) ≠ 1 := by
    intro h
    have h2 : (2 : K) = 0 := by linear_combination -h
    exact one_ne_zero (by linear_combination h3 - h2 : (1 : K) = 0)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : (0 : K) = -1 := by simpa using ha4
    exact one_ne_zero (neg_eq_zero.1 this.symm)
  have hmk : ∀ A B : SpecialLinearGroup (Fin 2) K, (QuotientGroup.mk A : PSL(2, K)) *
      QuotientGroup.mk B = QuotientGroup.mk (A * B) := fun A B => (QuotientGroup.mk_mul _ _ _).symm
  refine invNormalizer_of_cycle (u := QuotientGroup.mk (sl2U (1 : K)))
    (v := QuotientGroup.mk (sl2U (a ^ 2))) (x := QuotientGroup.mk (sl2D a ha0))
    (card_psl_two_of_card_nine hK) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← QuotientGroup.mk_pow, sl2U_pow_three h3, QuotientGroup.mk_one]
  · intro h
    have h0 : (QuotientGroup.mk (sl2U (0 : K)) : PSL(2, K)) = 1 := by
      rw [sl2U_zero]
      rfl
    exact one_ne_zero (mk_sl2U_injective (h.trans h0.symm))
  · rw [mul_inv_eq_iff_eq_mul, hmk, hmk, sl2D_mul_sl2U a ha0 1, mul_one]
  · rw [hmk, hmk, sl2U_add, sl2U_add, add_comm]
  · intro h
    have := mk_sl2U_injective h
    have h4 : a ^ 4 = 1 := by
      calc a ^ 4 = (a ^ 2) ^ 2 := by ring
        _ = 1 := by rw [this]; norm_num
    exact hm1 (ha4.symm.trans h4)
  · intro h
    have h' : (QuotientGroup.mk (sl2U (a ^ 2)) : PSL(2, K)) = QuotientGroup.mk (sl2U 1 * sl2U 1) := by
      rw [h, sq, ← hmk]
    rw [sl2U_add] at h'
    have := mk_sl2U_injective h'
    have h4 : a ^ 4 = 1 := by
      calc a ^ 4 = (a ^ 2) ^ 2 := by ring
        _ = (1 + 1) ^ 2 := by rw [this]
        _ = 1 := by linear_combination h3
    exact hm1 (ha4.symm.trans h4)
  · have hinv : (QuotientGroup.mk (sl2U (1 : K)) : PSL(2, K))⁻¹ = QuotientGroup.mk (sl2U (-1)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [hmk, sl2U_add, add_neg_cancel, sl2U_zero]
      rfl
    rw [mul_inv_eq_iff_eq_mul, hinv]
    simp only [hmk]
    rw [sl2D_sq_mul_sl2U, ha4, mul_one]

end SL2

theorem invNormalizer_of_lieModel_psl_two {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSL 2 3 2) : InvNormalizer 3 X := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  let e' : X ≃* PSL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  haveI : Finite X := Finite.of_equiv _ e'.symm.toEquiv
  exact (invNormalizer_psl_two_of_card_nine hK9).of_mulEquiv e'.symm

end CFSG.LocalAnalysis.UniquenessCase.UC6

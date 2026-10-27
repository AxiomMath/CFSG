module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2OddGroup

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem pglAction_mk_mk (G : GL (Fin 2) K) (X Y : SL(2, K))
    (h : (G : Matrix (Fin 2) (Fin 2) K) * (X : Matrix (Fin 2) (Fin 2) K) =
      (Y : Matrix (Fin 2) (Fin 2) K) * G) :
    pglAction K (ProjGenLinGroup.mk G) (QuotientGroup.mk X : PSL2 K) = QuotientGroup.mk Y := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pglAction, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  have hGX : G * Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL Y * G :=
    Units.ext h
  rw [hGX, mul_inv_cancel_right]

theorem word1411_pglAction_mk (G : GL (Fin 2) K) (X N : SL(2, K))
    (h : (G : Matrix (Fin 2) (Fin 2) K) * (X : Matrix (Fin 2) (Fin 2) K) =
      ((N : Matrix (Fin 2) (Fin 2) K) * X) * G) :
    word1411 (pglAction K (ProjGenLinGroup.mk G)) (QuotientGroup.mk X : PSL2 K) 1 1 =
      QuotientGroup.mk N := by
  have hY := pglAction_mk_mk G X (N * X) (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact h)
  simp only [word1411, inv_one, mul_one, map_one, one_mul, hY]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mul_inv_cancel_right]

theorem word1411_psl2FieldAut_mk (σ : K ≃+* K) (X₁ X₂ X₃ N : SL(2, K))
    (h : Matrix.SpecialLinearGroup.map σ.toRingHom X₁ * X₁⁻¹ *
      (X₂ * Matrix.SpecialLinearGroup.map σ.toRingHom (X₂⁻¹ * X₃) * X₃⁻¹) = N) :
    word1411 (psl2FieldAut K σ) (QuotientGroup.mk X₁ : PSL2 K) (QuotientGroup.mk X₂)
      (QuotientGroup.mk X₃) = QuotientGroup.mk N := by
  have e : ∀ X : SL(2, K), psl2FieldAut K σ (QuotientGroup.mk X : PSL2 K) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom X) := fun X => by
    rw [psl2FieldAut_apply]
    exact psl2RingEquiv_mk σ X
  rw [← h]
  simp only [word1411, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, e]

theorem mem_center_of_coe_eq_neg_one_or_one {N : SL(2, K)}
    (hN : (N : Matrix (Fin 2) (Fin 2) K) = -1 ∨ (N : Matrix (Fin 2) (Fin 2) K) = 1) :
    N ∈ Subgroup.center SL(2, K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rcases hN with h | h
  · refine ⟨-1, by norm_num, ?_⟩
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · refine ⟨1, by norm_num, ?_⟩
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem coe_apply_zero_one_eq_zero_of_mem_center {N : SL(2, K)}
    (hN : N ∈ Subgroup.center SL(2, K)) : (N : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hN
  rw [← hc]
  simp

theorem orderOf_mk_eq_prime {N : SL(2, K)} {r : ℕ} (hr : r.Prime)
    (hN : (N : Matrix (Fin 2) (Fin 2) K) ^ r = -1 ∨ (N : Matrix (Fin 2) (Fin 2) K) ^ r = 1)
    (h01 : (N : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0) : orderOf (QuotientGroup.mk N : PSL2 K) = r := by
  have : Fact r.Prime := ⟨hr⟩
  refine orderOf_eq_prime ?_ fun h1 => h01 ?_
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_center_of_coe_eq_neg_one_or_one (by rwa [Matrix.SpecialLinearGroup.coe_pow])
  · exact coe_apply_zero_one_eq_zero_of_mem_center ((QuotientGroup.eq_one_iff N).mp h1)

theorem orderOf_mk_eq_twentyFive {N : SL(2, K)}
    (hN : (N : Matrix (Fin 2) (Fin 2) K) ^ 25 = -1 ∨ (N : Matrix (Fin 2) (Fin 2) K) ^ 25 = 1)
    (h01 : ((N : Matrix (Fin 2) (Fin 2) K) ^ 5) 0 1 ≠ 0) :
    orderOf (QuotientGroup.mk N : PSL2 K) = 25 := by
  have h25 : (QuotientGroup.mk N : PSL2 K) ^ 25 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_center_of_coe_eq_neg_one_or_one (by rwa [Matrix.SpecialLinearGroup.coe_pow])
  have hdvd : orderOf (QuotientGroup.mk N : PSL2 K) ∣ 5 ^ 2 := orderOf_dvd_of_pow_eq_one h25
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvd
  have hk2 : k = 2 := by
    by_contra hne
    have h5 : (QuotientGroup.mk N : PSL2 K) ^ 5 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hk']
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> norm_num
    apply h01
    rw [← Matrix.SpecialLinearGroup.coe_pow]
    exact coe_apply_zero_one_eq_zero_of_mem_center
      ((QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact h5))
  rw [hk', hk2]
  norm_num

theorem map_fin_two_of {L : Type*} (f : K → L) (a b c d : K) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K).map f = !![f a, f b; f c, f d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

section Q25

theorem exists_sq_eq_two_of_card_eq_25 [Finite K] (hK : Nat.card K = 25) :
    (5 : K) = 0 ∧ ∃ z : K, z ^ 2 = 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hchar : CharP K 5 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 5]; norm_num
  have h20 : (2 : K) ≠ 0 := fun h => one_ne_zero (α := K) (by linear_combination h5 - 2 * h)
  refine ⟨h5, ?_⟩
  obtain ⟨y, hy⟩ := (FiniteField.isSquare_iff hK2 h20).mpr (by
    rw [Fintype.card_eq_nat_card, hK]
    norm_num
    grind)
  exact ⟨y, by rw [sq, ← hy]⟩

@[expose] def q25X0 (z : K) : SL(2, K) := ⟨!![-1, 1 - z; 0, -1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def q25N0 {z : K} (hz : z ^ 2 = 2) : SL(2, K) :=
  ⟨!![1, 1 - z; -1 + z, -2 + 2 * z], by rw [Matrix.det_fin_two_of]; grind⟩

@[expose] def q25X1 : SL(2, K) := ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def q25N1 {z : K} (h5 : (5 : K) = 0) (hz : z ^ 2 = 2) : SL(2, K) :=
  ⟨!![1 - z, 1; 2 * z, 2 * z], by rw [Matrix.det_fin_two_of]; grind⟩

@[expose] def q25F1 (z : K) : SL(2, K) := ⟨!![z, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

@[expose] def q25F2 (z : K) : SL(2, K) := ⟨!![-1, 0; -z, -1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def q25F3 {z : K} (hz : z ^ 2 = 2) : SL(2, K) :=
  ⟨!![0, -1 - z; -1 + z, 0], by rw [Matrix.det_fin_two_of]; grind⟩

@[expose] def q25NF {z : K} (h5 : (5 : K) = 0) (hz : z ^ 2 = 2) : SL(2, K) :=
  ⟨!![1 + z, -2 + z; -2 - z, 2 - 2 * z], by rw [Matrix.det_fin_two_of]; grind⟩

variable {z : K} (h5 : (5 : K) = 0) (hz : z ^ 2 = 2)

include h5 hz

theorem not_isSquare_of_sq_eq_two [Finite K] (hK : Nat.card K = 25) : ¬ IsSquare z := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hchar : CharP K 5 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 5]; norm_num
  have hz0 : z ≠ 0 := by
    rintro rfl
    grind
  rw [FiniteField.isSquare_iff hK2 hz0, Fintype.card_eq_nat_card, hK]
  norm_num
  grind

theorem pow_five_eq_neg_of_sq_eq_two : z ^ 5 = -z := by grind

theorem q25N0_pow : ((q25N0 hz : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 13 = -1 := by
  change (!![1, 1 - z; -1 + z, -2 + 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 13 = -1
  have e2 : (!![1, 1 - z; -1 + z, -2 + 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      !![-2 + 2 * z, -2 * z; 2 * z, -1 - z] := by
    rw [sq]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e4 : (!![1, 1 - z; -1 + z, -2 + 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 4 =
      !![-1 + 2 * z, 1 + z; -1 - z, 2 * z] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e8 : (!![1, 1 - z; -1 + z, -2 + 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 8 =
      !![1 - z, 2 - 2 * z; -2 + 2 * z, -2 * z] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  rw [show 13 = 8 + 4 + 1 from rfl, pow_add, pow_add, e8, e4, pow_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem q25N1_pow : ((q25N1 h5 hz : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 13 = -1 := by
  change (!![1 - z, 1; 2 * z, 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 13 = -1
  have e2 : (!![1 - z, 1; 2 * z, 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      !![-2, 1 + z; -1 + 2 * z, -2 + 2 * z] := by
    rw [sq]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e4 : (!![1 - z, 1; 2 * z, 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 4 =
      !![2 + z, -2 * z; 2, -2 * z] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e8 : (!![1 - z, 1; 2 * z, 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 8 =
      !![1, -1 + z; -1 - 2 * z, -2 + z] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  rw [show 13 = 8 + 4 + 1 from rfl, pow_add, pow_add, e8, e4, pow_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem q25NF_pow : ((q25NF h5 hz : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 13 = -1 := by
  change (!![1 + z, -2 + z; -2 - z, 2 - 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 13 = -1
  have e2 : (!![1 + z, -2 + z; -2 - z, 2 - 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      !![2 * z, 2; 1 - z, -1 + 2 * z] := by
    rw [sq]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e4 : (!![1 + z, -2 + z; -2 - z, 2 - 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 4 =
      !![-2 * z, -2 - 2 * z; 1, 1 - z] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e8 : (!![1 + z, -2 + z; -2 - z, 2 - 2 * z] : Matrix (Fin 2) (Fin 2) K) ^ 8 =
      !![1 - 2 * z, -z; 1 + 2 * z, 1 + z] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  rw [show 13 = 8 + 4 + 1 from rfl, pow_add, pow_add, e8, e4, pow_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem exists_word1411_L2_25_normalForms [Finite K] (hK : Nat.card K = 25) :
    (∃ x₁ x₂ x₃ : PSL2 K,
      13 ∣ orderOf (word1411 (pglAction K (ProjGenLinGroup.mk (swapGL 1))) x₁ x₂ x₃)) ∧
    (∃ x₁ x₂ x₃ : PSL2 K, 13 ∣ orderOf (word1411 (pglAction K
      (ProjGenLinGroup.mk (swapGL (Units.mk0 z (fun h0 => not_isSquare_of_sq_eq_two h5 hz hK
        (by rw [h0]; exact ⟨0, by ring⟩)))))) x₁ x₂ x₃)) ∧
    ∀ σ : K ≃+* K, (∀ x, σ x = x ^ 5) →
      ∃ x₁ x₂ x₃ : PSL2 K, 13 ∣ orderOf (word1411 (psl2FieldAut K σ) x₁ x₂ x₃) := by
  have h13 : Nat.Prime 13 := by norm_num
  refine ⟨⟨QuotientGroup.mk (q25X0 z), 1, 1, ?_⟩, ⟨QuotientGroup.mk q25X1, 1, 1, ?_⟩,
    fun σ hσ => ⟨QuotientGroup.mk (q25F1 z), QuotientGroup.mk (q25F2 z),
      QuotientGroup.mk (q25F3 hz), ?_⟩⟩
  · rw [word1411_pglAction_mk _ _ (q25N0 hz) ?_,
      orderOf_mk_eq_prime h13 (Or.inl (q25N0_pow h5 hz)) ?_]
    · change (1 : K) - z ≠ 0
      intro h0
      grind
    · rw [coe_swapGL]
      change !![0, ((1 : Kˣ) : K); 1, 0] * !![-1, 1 - z; 0, -1] =
        !![1, 1 - z; -1 + z, -2 + 2 * z] * !![-1, 1 - z; 0, -1] * !![0, ((1 : Kˣ) : K); 1, 0]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · rw [word1411_pglAction_mk _ _ (q25N1 h5 hz) ?_,
      orderOf_mk_eq_prime h13 (Or.inl (q25N1_pow h5 hz)) ?_]
    · change (1 : K) ≠ 0
      exact one_ne_zero
    · rw [coe_swapGL]
      change !![0, z; 1, 0] * !![0, 1; -1, -1] =
        !![1 - z, 1; 2 * z, 2 * z] * !![0, 1; -1, -1] * !![0, z; 1, 0]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · have hσz : σ z = -z := by rw [hσ]; exact pow_five_eq_neg_of_sq_eq_two h5 hz
    rw [word1411_psl2FieldAut_mk σ _ _ _ (q25NF h5 hz) ?_,
      orderOf_mk_eq_prime h13 (Or.inl (q25NF_pow h5 hz)) ?_]
    · change (-2 : K) + z ≠ 0
      intro h0
      have hz2 : z = 2 := by linear_combination h0
      rw [hz2] at hz
      exact one_ne_zero (α := K) (by linear_combination h5 - 2 * hz)
    · apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      change (!![z, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K).map σ *
          adjugate !![z, -1; 1, 0] * (!![-1, 0; -z, -1] *
          (adjugate !![-1, 0; -z, -1] * !![0, -1 - z; -1 + z, 0]).map σ *
          adjugate !![0, -1 - z; -1 + z, 0]) = !![1 + z, -2 + z; -2 - z, 2 - 2 * z]
      simp only [Matrix.adjugate_fin_two_of, Matrix.mul_fin_two, map_fin_two_of, map_add, map_sub,
        map_neg, map_mul, map_one, map_zero, map_ofNat, hσz]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> grind

end Q25

theorem exists_word1411_L2_25 [Finite K] (hK : Nat.card K = 25) (α : MulAut (PSL2 K))
    (hα : orderOf α = 2) : ∃ x₁ x₂ x₃ : PSL2 K, 13 ∣ orderOf (word1411 α x₁ x₂ x₃) := by
  obtain ⟨h5, z, hz⟩ := exists_sq_eq_two_of_card_eq_25 hK
  have hν := not_isSquare_of_sq_eq_two h5 hz hK
  obtain ⟨h0, h1, h2⟩ := exists_word1411_L2_25_normalForms h5 hz hK
  exact exists_dvd_orderOf_word1411 (p := 5) (by norm_num) (by norm_num) (by rw [hK]; norm_num)
    _ hν h0 h1 h2 α hα

section Q49

theorem exists_sq_eq_three_of_card_eq_49 [Finite K] (hK : Nat.card K = 49) :
    (7 : K) = 0 ∧ ∃ z : K, z ^ 2 = 3 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hchar : CharP K 7 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have h7 : (7 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 7
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 7]; norm_num
  have h30 : (3 : K) ≠ 0 := fun h => one_ne_zero (α := K) (by linear_combination h7 - 2 * h)
  refine ⟨h7, ?_⟩
  obtain ⟨y, hy⟩ := (FiniteField.isSquare_iff hK2 h30).mpr (by
    rw [Fintype.card_eq_nat_card, hK]
    norm_num
    grind)
  exact ⟨y, by rw [sq, ← hy]⟩

@[expose] def q49X0 {z : K} (hz : z ^ 2 = 3) : SL(2, K) :=
  ⟨!![z, 1; 2 + z, 1 + z], by rw [Matrix.det_fin_two_of]; grind⟩

@[expose] def q49N0 {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : SL(2, K) :=
  ⟨!![-3 - 2 * z, 2 + z; -2 - z, 2], by rw [Matrix.det_fin_two_of]; grind⟩

@[expose] def q49X1 {z : K} (hz : z ^ 2 = 3) : SL(2, K) :=
  ⟨!![z, 1 + z; 2, 2 + z], by rw [Matrix.det_fin_two_of]; grind⟩

@[expose] def q49N1 {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : SL(2, K) :=
  ⟨!![3, 1 - z; 2 - z, 2 - z], by rw [Matrix.det_fin_two_of]; grind⟩

@[expose] def q49F1 {z : K} (hz : z ^ 2 = 3) : SL(2, K) :=
  ⟨!![z, 1; 2, z], by rw [Matrix.det_fin_two_of]; grind⟩

@[expose] def q49F3 {z : K} (hz : z ^ 2 = 3) : SL(2, K) :=
  ⟨!![z, 2; 1, z], by rw [Matrix.det_fin_two_of]; grind⟩

@[expose] def q49NF {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3) : SL(2, K) :=
  ⟨!![-2 - 2 * z, 3 + 3 * z; 3 + 3 * z, 1 - 3 * z], by rw [Matrix.det_fin_two_of]; grind⟩

variable {z : K} (h7 : (7 : K) = 0) (hz : z ^ 2 = 3)

include h7 hz

theorem not_isSquare_one_add_of_sq_eq_three [Finite K] (hK : Nat.card K = 49) :
    ¬ IsSquare (1 + z) := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hchar : CharP K 7 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 7]; norm_num
  have h0 : 1 + z ≠ 0 := by
    intro h0
    have hz1 : z = -1 := by linear_combination h0
    rw [hz1] at hz
    exact one_ne_zero (α := K) (by linear_combination 3 * hz + h7)
  have h8 : (1 + z) ^ 8 = -2 := by grind
  rw [FiniteField.isSquare_iff hK2 h0, Fintype.card_eq_nat_card, hK]
  norm_num
  intro h24
  have h3 : ((1 + z) ^ 8) ^ 3 = 1 := by rw [← pow_mul]; exact h24
  rw [h8] at h3
  exact one_ne_zero (α := K) (by linear_combination 3 * h3 + 4 * h7)

theorem pow_seven_eq_neg_of_sq_eq_three : z ^ 7 = -z := by grind

theorem q49N0_pow : ((q49N0 h7 hz : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 25 = -1 ∧
    (((q49N0 h7 hz : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 5) 0 1 = -3 - z := by
  change (!![-3 - 2 * z, 2 + z; -2 - z, 2] : Matrix (Fin 2) (Fin 2) K) ^ 25 = -1 ∧
    ((!![-3 - 2 * z, 2 + z; -2 - z, 2] : Matrix (Fin 2) (Fin 2) K) ^ 5) 0 1 = -3 - z
  have e2 : (!![-3 - 2 * z, 2 + z; -2 - z, 2] : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      !![z, -1 + 2 * z; 1 - 2 * z, -3 + 3 * z] := by
    rw [sq]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e4 : (!![-3 - 2 * z, 2 + z; -2 - z, 2] : Matrix (Fin 2) (Fin 2) K) ^ 4 =
      !![-3 - 3 * z, -1 - 3 * z; 1 + 3 * z, 2] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e8 : (!![-3 - 2 * z, 2 + z; -2 - z, 2] : Matrix (Fin 2) (Fin 2) K) ^ 8 =
      !![1 - 2 * z, -z; z, -3 + z] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e16 : (!![-3 - 2 * z, 2 + z; -2 - z, 2] : Matrix (Fin 2) (Fin 2) K) ^ 16 =
      !![3 + 3 * z, 3 + 2 * z; -3 - 2 * z, 2 + z] := by
    rw [show 16 = 8 + 8 from rfl, pow_add, e8]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  constructor
  · rw [show 25 = 16 + 8 + 1 from rfl, pow_add, pow_add, e16, e8, pow_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · rw [show 5 = 4 + 1 from rfl, pow_add, e4, pow_one]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    grind

theorem q49N1_pow : ((q49N1 h7 hz : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 25 = 1 ∧
    (((q49N1 h7 hz : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 5) 0 1 = 1 + 2 * z := by
  change (!![3, 1 - z; 2 - z, 2 - z] : Matrix (Fin 2) (Fin 2) K) ^ 25 = 1 ∧
    ((!![3, 1 - z; 2 - z, 2 - z] : Matrix (Fin 2) (Fin 2) K) ^ 5) 0 1 = 1 + 2 * z
  have e2 : (!![3, 1 - z; 2 - z, 2 - z] : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      !![-3 * z, 1 + z; -1, -2] := by
    rw [sq]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e4 : (!![3, 1 - z; 2 - z, 2 - z] : Matrix (Fin 2) (Fin 2) K) ^ 4 =
      !![-2 - z, 3 + 2 * z; 2 + 3 * z, 3 - z] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e8 : (!![3, 1 - z; 2 - z, 2 - z] : Matrix (Fin 2) (Fin 2) K) ^ 8 =
      !![3 + 3 * z, -2 + 3 * z; -2 - z, 1] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e16 : (!![3, 1 - z; 2 - z, 2 - z] : Matrix (Fin 2) (Fin 2) K) ^ 16 =
      !![3, -2 - z; -3 - 3 * z, 3 + 3 * z] := by
    rw [show 16 = 8 + 8 from rfl, pow_add, e8]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  constructor
  · rw [show 25 = 16 + 8 + 1 from rfl, pow_add, pow_add, e16, e8, pow_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · rw [show 5 = 4 + 1 from rfl, pow_add, e4, pow_one]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    grind

theorem q49NF_pow : ((q49NF h7 hz : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 25 = -1 ∧
    (((q49NF h7 hz : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 5) 0 1 = 3 + 2 * z := by
  change (!![-2 - 2 * z, 3 + 3 * z; 3 + 3 * z, 1 - 3 * z] : Matrix (Fin 2) (Fin 2) K) ^ 25 = -1 ∧
    ((!![-2 - 2 * z, 3 + 3 * z; 3 + 3 * z, 1 - 3 * z] : Matrix (Fin 2) (Fin 2) K) ^ 5) 0 1 =
      3 + 2 * z
  have e2 : (!![-2 - 2 * z, 3 + 3 * z; 3 + 3 * z, 1 - 3 * z] : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      !![3 - 2 * z, 1 + 3 * z; 1 + 3 * z, 1 - 2 * z] := by
    rw [sq]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e4 : (!![-2 - 2 * z, 3 + 3 * z; 3 + 3 * z, 1 - 3 * z] : Matrix (Fin 2) (Fin 2) K) ^ 4 =
      !![z, 3 + z; 3 + z, -1 + 2 * z] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e8 : (!![-2 - 2 * z, 3 + 3 * z; 3 + 3 * z, 1 - 3 * z] : Matrix (Fin 2) (Fin 2) K) ^ 8 =
      !![1 - z, -1 + z; -1 + z, -3 + 2 * z] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e16 : (!![-2 - 2 * z, 3 + 3 * z; 3 + 3 * z, 1 - 3 * z] : Matrix (Fin 2) (Fin 2) K) ^ 16 =
      !![1 + 3 * z, -2 - 3 * z; -2 - 3 * z, -3] := by
    rw [show 16 = 8 + 8 from rfl, pow_add, e8]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  constructor
  · rw [show 25 = 16 + 8 + 1 from rfl, pow_add, pow_add, e16, e8, pow_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · rw [show 5 = 4 + 1 from rfl, pow_add, e4, pow_one]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    grind

theorem exists_word1411_L2_49_normalForms [Finite K] (hK : Nat.card K = 49) :
    (∃ x₁ x₂ x₃ : PSL2 K,
      25 ∣ orderOf (word1411 (pglAction K (ProjGenLinGroup.mk (swapGL 1))) x₁ x₂ x₃)) ∧
    (∃ x₁ x₂ x₃ : PSL2 K, 25 ∣ orderOf (word1411 (pglAction K
      (ProjGenLinGroup.mk (swapGL (Units.mk0 (1 + z) (fun h0 =>
        not_isSquare_one_add_of_sq_eq_three h7 hz hK
          (by rw [h0]; exact ⟨0, by ring⟩)))))) x₁ x₂ x₃)) ∧
    ∀ σ : K ≃+* K, (∀ x, σ x = x ^ 7) →
      ∃ x₁ x₂ x₃ : PSL2 K, 25 ∣ orderOf (word1411 (psl2FieldAut K σ) x₁ x₂ x₃) := by
  refine ⟨⟨QuotientGroup.mk (q49X0 hz), 1, 1, ?_⟩, ⟨QuotientGroup.mk (q49X1 hz), 1, 1, ?_⟩,
    fun σ hσ => ⟨QuotientGroup.mk (q49F1 hz), QuotientGroup.mk (q49X0 hz),
      QuotientGroup.mk (q49F3 hz), ?_⟩⟩
  · obtain ⟨hp, h01⟩ := q49N0_pow h7 hz
    rw [word1411_pglAction_mk _ _ (q49N0 h7 hz) ?_,
      orderOf_mk_eq_twentyFive (Or.inl hp) ?_]
    · rw [h01]
      intro h0
      have hz3 : z = -3 := by linear_combination -h0
      rw [hz3] at hz
      exact one_ne_zero (α := K) (by linear_combination h7 - hz)
    · rw [coe_swapGL]
      change !![0, ((1 : Kˣ) : K); 1, 0] * !![z, 1; 2 + z, 1 + z] =
        !![-3 - 2 * z, 2 + z; -2 - z, 2] * !![z, 1; 2 + z, 1 + z] * !![0, ((1 : Kˣ) : K); 1, 0]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · obtain ⟨hp, h01⟩ := q49N1_pow h7 hz
    rw [word1411_pglAction_mk _ _ (q49N1 h7 hz) ?_,
      orderOf_mk_eq_twentyFive (Or.inr hp) ?_]
    · rw [h01]
      intro h0
      exact one_ne_zero (α := K) (by linear_combination 2 * (2 * z - 1) * h0 - 8 * hz - 3 * h7)
    · rw [coe_swapGL]
      change !![0, 1 + z; 1, 0] * !![z, 1 + z; 2, 2 + z] =
        !![3, 1 - z; 2 - z, 2 - z] * !![z, 1 + z; 2, 2 + z] * !![0, 1 + z; 1, 0]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · have hσz : σ z = -z := by rw [hσ]; exact pow_seven_eq_neg_of_sq_eq_three h7 hz
    obtain ⟨hp, h01⟩ := q49NF_pow h7 hz
    rw [word1411_psl2FieldAut_mk σ _ _ _ (q49NF h7 hz) ?_,
      orderOf_mk_eq_twentyFive (Or.inl hp) ?_]
    · rw [h01]
      intro h0
      exact one_ne_zero (α := K) (by linear_combination -2 * (2 * z - 3) * h0 + 8 * hz + h7)
    · apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      change (!![z, 1; 2, z] : Matrix (Fin 2) (Fin 2) K).map σ *
          adjugate !![z, 1; 2, z] * (!![z, 1; 2 + z, 1 + z] *
          (adjugate !![z, 1; 2 + z, 1 + z] * !![z, 2; 1, z]).map σ *
          adjugate !![z, 2; 1, z]) = !![-2 - 2 * z, 3 + 3 * z; 3 + 3 * z, 1 - 3 * z]
      simp only [Matrix.adjugate_fin_two_of, Matrix.mul_fin_two, map_fin_two_of, map_add, map_sub,
        map_neg, map_mul, map_one, map_zero, map_ofNat, hσz]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> grind

end Q49

theorem exists_word1411_L2_49 [Finite K] (hK : Nat.card K = 49) (α : MulAut (PSL2 K))
    (hα : orderOf α = 2) : ∃ x₁ x₂ x₃ : PSL2 K, 25 ∣ orderOf (word1411 α x₁ x₂ x₃) := by
  obtain ⟨h7, z, hz⟩ := exists_sq_eq_three_of_card_eq_49 hK
  have hν := not_isSquare_one_add_of_sq_eq_three h7 hz hK
  obtain ⟨h0, h1, h2⟩ := exists_word1411_L2_49_normalForms h7 hz hK
  exact exists_dvd_orderOf_word1411 (p := 7) (by norm_num) (by norm_num) (by rw [hK]; norm_num)
    _ hν h0 h1 h2 α hα

end CFSG.RankThree.PartTwo.Sec20

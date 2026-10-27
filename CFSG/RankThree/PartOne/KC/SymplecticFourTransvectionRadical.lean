module

public import CFSG.RankThree.PartOne.KC.SymplecticFourTransvectionDefs

public section

namespace CFSG.RankThree.PartOne.KCSymplecticFour

open Matrix

variable {K : Type} [Field K]

@[expose] def uMat (s t b : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, -t, s, b; 0, 1, 0, s; 0, 0, 1, t; 0, 0, 0, 1]

theorem uMat_zero : uMat (0 : K) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMat_mul (s t b s' t' b' : K) :
    uMat s t b * uMat s' t' b' = uMat (s + s') (t + t') (b + b' + (s * t' - t * s')) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uMat_map (σ : K ≃+* K) (s t b : K) : (uMat s t b).map σ = uMat (σ s) (σ t) (σ b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMat_mem (s t b : K) :
    (uMat s t b)ᵀ * symplecticFourGram K * uMat s t b = symplecticFourGram K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, symplecticFourGram, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem uMat_mul_neg (s t b : K) : uMat s t b * uMat (-s) (-t) (-b) = 1 := by
  rw [uMat_mul, ← uMat_zero]
  congr 1 <;> ring

theorem uMat_neg_mul (s t b : K) : uMat (-s) (-t) (-b) * uMat s t b = 1 := by
  rw [uMat_mul, ← uMat_zero]
  congr 1 <;> ring

theorem uMat_comm_E14 (s t b : K) :
    uMat s t b * symplecticFourE14 K = symplecticFourE14 K * uMat s t b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, symplecticFourE14, Matrix.mul_apply, Matrix.single_apply]

theorem uMat_zero_zero (b : K) : uMat 0 0 b = 1 + b • symplecticFourE14 K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, symplecticFourE14]

@[expose] def uElt (s t b : K) : symplecticFourS K :=
  ⟨⟨uMat s t b, uMat (-s) (-t) (-b), uMat_mul_neg s t b, uMat_neg_mul s t b⟩, uMat_mem s t b⟩

theorem coe_uElt (s t b : K) :
    (((uElt s t b : symplecticFourS K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      uMat s t b :=
  rfl

@[expose] def radical (K : Type) [Field K] : Subgroup (symplecticFourS K) where
  carrier := {g | ∃ s t b : K,
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = uMat s t b}
  mul_mem' := by
    rintro g h ⟨s, t, b, hg⟩ ⟨s', t', b', hh⟩
    exact ⟨s + s', t + t', b + b' + (s * t' - t * s'), by
      rw [Subgroup.coe_mul, Units.val_mul, hg, hh, uMat_mul]⟩
  one_mem' := ⟨0, 0, 0, by rw [uMat_zero]; rfl⟩
  inv_mem' := by
    rintro g ⟨s, t, b, hg⟩
    refine ⟨-s, -t, -b, ?_⟩
    rw [Subgroup.coe_inv, Matrix.coe_units_inv, hg]
    exact Matrix.inv_eq_right_inv (uMat_mul_neg s t b)

theorem uElt_mem_radical (s t b : K) : uElt s t b ∈ radical K :=
  ⟨s, t, b, rfl⟩

theorem uMat_pow (s t b : K) (n : ℕ) : uMat s t b ^ n = uMat (n * s) (n * t) (n * b) := by
  induction n with
  | zero => simp [uMat_zero]
  | succ n ih =>
    rw [pow_succ, ih, uMat_mul]
    congr 1 <;> push_cast <;> ring

theorem uMat_pow_char {p : ℕ} [CharP K p] (s t b : K) : uMat s t b ^ p = 1 := by
  rw [uMat_pow, CharP.cast_eq_zero K p, zero_mul, zero_mul, zero_mul, uMat_zero]

theorem pow_char_eq_one_of_mem_radical {p : ℕ} [CharP K p] {y : symplecticFourS K}
    (hy : y ∈ radical K) : y ^ p = 1 := by
  obtain ⟨s, t, b, hy⟩ := hy
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hy, uMat_pow_char]
  rfl

theorem radical_comm_transvection {y : symplecticFourS K} (hy : y ∈ radical K) (c : K) :
    y * symplecticFourTransvection K c = symplecticFourTransvection K c * y := by
  obtain ⟨s, t, b, hy⟩ := hy
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hy,
    coe_symplecticFourTransvection, mul_add, add_mul, mul_one, one_mul, mul_smul_comm,
    smul_mul_assoc, uMat_comm_E14]

theorem entries_of_comm_E14 {G : Matrix (Fin 4) (Fin 4) K}
    (h : G * symplecticFourE14 K = symplecticFourE14 K * G) :
    G 1 0 = 0 ∧ G 2 0 = 0 ∧ G 3 0 = 0 ∧ G 3 1 = 0 ∧ G 3 2 = 0 ∧ G 3 3 = G 0 0 := by
  have e : ∀ i j, (G * symplecticFourE14 K) i j = (symplecticFourE14 K * G) i j :=
    fun i j => by rw [h]
  have e13 := e 1 3
  have e23 := e 2 3
  have e33 := e 3 3
  have e01 := e 0 1
  have e02 := e 0 2
  have e03 := e 0 3
  simp [symplecticFourE14, Matrix.mul_apply, Matrix.single_apply] at e13 e23 e33 e01 e02 e03
  exact ⟨e13, e23, e33, e01.symm, e02.symm, e03.symm⟩

theorem gram_conj_apply (G : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (Gᵀ * symplecticFourGram K * G) i j =
      G 0 i * G 3 j - G 3 i * G 0 j + G 1 i * G 2 j - G 2 i * G 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, symplecticFourGram]
  ring

theorem mul_uMat_eq {G : Matrix (Fin 4) (Fin 4) K}
    (hc : G * symplecticFourE14 K = symplecticFourE14 K * G)
    (hi : Gᵀ * symplecticFourGram K * G = symplecticFourGram K) (s t b : K) :
    ∃ s' t' b' : K, G * uMat s t b = uMat s' t' b' * G := by
  obtain ⟨h10, h20, h30, h31, h32, h33⟩ := entries_of_comm_E14 hc
  have i03 := gram_conj_apply G 0 3
  have i12 := gram_conj_apply G 1 2
  have i13 := gram_conj_apply G 1 3
  have i23 := gram_conj_apply G 2 3
  rw [hi] at i03 i12 i13 i23
  simp [symplecticFourGram] at i03 i12 i13 i23
  refine ⟨G 0 0 * (G 1 1 * s + G 1 2 * t), G 0 0 * (G 2 1 * s + G 2 2 * t),
    b + G 0 0 * (G 0 1 * s + G 0 2 * t + (G 0 0 * (G 2 1 * s + G 2 2 * t)) * G 1 3 -
      (G 0 0 * (G 1 1 * s + G 1 2 * t)) * G 2 3), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_four, h10, h20, h30, h31, h32, h33] <;> grind

theorem conj_mem_radical_of_commute {g : symplecticFourS K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * symplecticFourE14 K =
      symplecticFourE14 K * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    {y : symplecticFourS K} (hy : y ∈ radical K) : g * y * g⁻¹ ∈ radical K := by
  obtain ⟨s, t, b, hy⟩ := hy
  obtain ⟨s', t', b', h⟩ := mul_uMat_eq hg (mem_symplecticFourS_iff.mp g.2) s t b
  have hmul : g * y = uElt s' t' b' * g := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hy, coe_uElt]
    exact h
  rw [hmul, mul_inv_cancel_right]
  exact uElt_mem_radical s' t' b'

end CFSG.RankThree.PartOne.KCSymplecticFour

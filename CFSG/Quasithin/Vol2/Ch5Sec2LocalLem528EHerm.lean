module

public import CFSG.Quasithin.Background.B4ModelsLie

public section

namespace CFSG.Quasithin.H13.Herm

open Matrix CFSG.Quasithin

variable {F : Type} [Field F] [CharP F 2]

theorem frobPow_eq_mapMatrix (a : ℕ) (X : Matrix (Fin 2) (Fin 2) F) :
    frobPow a X = (iterateFrobenius F 2 a).mapMatrix X := by
  ext i j
  simp [frobPow, iterateFrobenius_def]

theorem mul_self_eq_of_det_eq_one {A : Matrix (Fin 2) (Fin 2) F} (hA : A.det = 1) :
    A * A = A.trace • A + 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [Matrix.det_fin_two] at hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination (-1 : F) * hA - h2

theorem trace_frob_eq_of_pow_eq {a : ℕ} {A : Matrix (Fin 2) (Fin 2) F} (hA : A.det = 1)
    (hpow : A ^ 2 ^ a = A) : A.trace ^ 2 ^ a = A.trace := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCH := mul_self_eq_of_det_eq_one hA
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hneg : ∀ y : F, -y = y := fun y => by
    have : y + y = 0 := by rw [← two_mul, h2, zero_mul]
    exact neg_eq_of_add_eq_zero_left this
  have h0 : A * A + (A.trace • A + 1) = 0 := by
    rw [hCH, ← two_smul F (A.trace • A + 1)]
    rw [h2, zero_smul]
  have hc1 : Commute (A * A) (A.trace • A + 1) :=
    ((Commute.mul_left (Commute.refl A) (Commute.refl A)).smul_right A.trace).add_right
      (Commute.one_right _) |>.symm.symm
  have hc2 : Commute (A.trace • A) (1 : Matrix (Fin 2) (Fin 2) F) := Commute.one_right _
  have hfrob := congrArg (fun Y : Matrix (Fin 2) (Fin 2) F => Y ^ 2 ^ a) h0
  rw [add_pow_char_pow_of_commute 2 a hc1,
    add_pow_char_pow_of_commute 2 a hc2, smul_pow, one_pow,
    zero_pow (pow_ne_zero a two_ne_zero)] at hfrob
  have hAA : (A * A) ^ 2 ^ a = A * A := by
    rw [(Commute.refl A).mul_pow, hpow]
  rw [hAA, hpow] at hfrob
  have hdiff : (A.trace ^ 2 ^ a - A.trace) • A = 0 := by
    rw [sub_smul]
    have e1 : A.trace ^ 2 ^ a • A = -(A * A + 1) := by
      rw [eq_neg_iff_add_eq_zero]
      rw [show A.trace ^ 2 ^ a • A + (A * A + 1) = A * A + (A.trace ^ 2 ^ a • A + 1) by abel]
      exact hfrob
    have e2 : A.trace • A = -(A * A + 1) := by
      rw [eq_neg_iff_add_eq_zero]
      rw [show A.trace • A + (A * A + 1) = A * A + (A.trace • A + 1) by abel]
      exact h0
    rw [e1, e2, sub_self]
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, Matrix.det_zero] at hA
    exact zero_ne_one hA
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hcon
    apply hA0
    ext i j
    by_contra h
    exact hcon ⟨i, j, h⟩
  have := congrFun (congrFun hdiff i) j
  rw [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul, mul_eq_zero] at this
  rcases this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hij

@[expose] def compMat (t : F) : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, t]

@[expose] def jMat : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

theorem compMat_jMat (t : F) :
    compMat t * jMat * (compMat t)ᵀ = (jMat : Matrix (Fin 2) (Fin 2) F) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compMat, jMat, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination t * h2

@[expose] def colMat (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F :=
  !![v 0, (A *ᵥ v) 0; v 1, (A *ᵥ v) 1]

theorem mul_colMat {A : Matrix (Fin 2) (Fin 2) F} (hA : A.det = 1) (v : Fin 2 → F) :
    A * colMat A v = colMat A v * compMat A.trace := by
  have hCH := mul_self_eq_of_det_eq_one hA
  have hAA : ∀ i : Fin 2, (A *ᵥ (A *ᵥ v)) i = A.trace * (A *ᵥ v) i + v i := by
    intro i
    rw [Matrix.mulVec_mulVec, hCH, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e0 := hAA 0
  have e1 := hAA 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colMat, compMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;>
    first | ring1 | linear_combination e0 | linear_combination e1

theorem exists_colMat_det_ne_zero {A : Matrix (Fin 2) (Fin 2) F} (hA : A.det = 1)
    (hA1 : A ≠ 1) : ∃ v : Fin 2 → F, (colMat A v).det ≠ 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [Matrix.det_fin_two] at hA
  by_cases h10 : A 1 0 = 0
  · by_cases h01 : A 0 1 = 0
    · refine ⟨![1, 1], ?_⟩
      intro hd
      simp [colMat, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10,
        h01] at hd
      have hd' : A 1 1 = A 0 0 := by linear_combination hd
      rw [h10, h01, mul_zero, sub_zero, hd'] at hA
      have hsq : (A 0 0 - 1) ^ 2 = 0 := by linear_combination hA + (1 - A 0 0) * h2
      have h00 : A 0 0 = 1 := sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hsq)
      apply hA1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h10, h01, hd']
    · refine ⟨![0, 1], ?_⟩
      intro hd
      simp [colMat, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hd
      exact h01 hd
  · refine ⟨![1, 0], ?_⟩
    intro hd
    simp [colMat, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hd
    exact h10 hd

omit [CharP F 2] in
theorem frobPow_jMat (a : ℕ) : frobPow a (jMat : Matrix (Fin 2) (Fin 2) F) = jMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow, jMat]

omit [CharP F 2] in
theorem frobPow_compMat {a : ℕ} {t : F} (ht : t ^ 2 ^ a = t) :
    frobPow a (compMat t) = compMat t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow, compMat, ht]

theorem frobPow_mul (a : ℕ) (M N : Matrix (Fin 2) (Fin 2) F) :
    frobPow a (M * N) = frobPow a M * frobPow a N := by
  rw [frobPow_eq_mapMatrix, frobPow_eq_mapMatrix, frobPow_eq_mapMatrix, map_mul]

omit [CharP F 2] in
theorem frobPow_transpose (a : ℕ) (M : Matrix (Fin 2) (Fin 2) F) :
    frobPow a Mᵀ = (frobPow a M)ᵀ := by
  ext i j
  simp [frobPow]

theorem exists_herm_fixed {a : ℕ} (hσ : ∀ x : F, (x ^ 2 ^ a) ^ 2 ^ a = x)
    {A : Matrix (Fin 2) (Fin 2) F} (hA : A.det = 1) (hA1 : A ≠ 1) (hpow : A ^ 2 ^ a = A) :
    ∃ X : Matrix (Fin 2) (Fin 2) F, X ≠ 0 ∧ (frobPow a X)ᵀ = X ∧
      A * X * (frobPow a A)ᵀ = X := by
  obtain ⟨v, hv⟩ := exists_colMat_det_ne_zero hA hA1
  set P := colMat A v with hP
  have hτ := trace_frob_eq_of_pow_eq hA hpow
  have hσσ : frobPow a (frobPow a P) = P := by
    ext i j
    simp [frobPow, hσ]
  have hAP := mul_colMat hA v
  rw [← hP] at hAP
  refine ⟨P * jMat * (frobPow a P)ᵀ, ?_, ?_, ?_⟩
  · intro h0
    have hdet := congrArg Matrix.det h0
    rw [Matrix.det_zero, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
    have hJ : (jMat : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      simp [jMat, Matrix.det_fin_two]
    have hσP : (frobPow a P).det ≠ 0 := by
      rw [frobPow_eq_mapMatrix, ← RingHom.map_det]
      exact (iterateFrobenius F 2 a).injective.ne_iff.mpr hv |>.trans_eq (map_zero _) |> fun h =>
        by simpa using h
    exact mul_ne_zero (mul_ne_zero hv hJ) hσP hdet
  · rw [frobPow_mul, frobPow_mul, frobPow_transpose, hσσ, frobPow_jMat, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose,
      show (jMat : Matrix (Fin 2) (Fin 2) F)ᵀ = jMat by ext i j; fin_cases i <;> fin_cases j <;>
        simp [jMat], Matrix.mul_assoc]
  · have h1 : frobPow a A * frobPow a P = frobPow a P * compMat A.trace := by
      rw [← frobPow_mul, hAP, frobPow_mul, frobPow_compMat hτ]
    calc A * (P * jMat * (frobPow a P)ᵀ) * (frobPow a A)ᵀ
        = (A * P) * jMat * ((frobPow a A) * (frobPow a P))ᵀ := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (P * compMat A.trace) * jMat * (frobPow a P * compMat A.trace)ᵀ := by rw [hAP, h1]
      _ = P * (compMat A.trace * jMat * (compMat A.trace)ᵀ) * (frobPow a P)ᵀ := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = P * jMat * (frobPow a P)ᵀ := by rw [compMat_jMat]

theorem frobPow_add (a : ℕ) (X Y : Matrix (Fin 2) (Fin 2) F) :
    frobPow a (X + Y) = frobPow a X + frobPow a Y := by
  ext i j
  simp only [frobPow, Matrix.map_apply, Matrix.add_apply]
  exact add_pow_char_pow _ _ 2 a

@[expose] def hermTrace (a : ℕ) :
    Multiplicative (Matrix (Fin 2) (Fin 2) F) →* Multiplicative (Matrix (Fin 2) (Fin 2) F) where
  toFun X := Multiplicative.ofAdd
    (Multiplicative.toAdd X + (frobPow a (Multiplicative.toAdd X))ᵀ)
  map_one' := by
    have h0 : frobPow a (0 : Matrix (Fin 2) (Fin 2) F) = 0 := by
      ext i j
      simp [frobPow]
    simp [h0]
  map_mul' X Y := by
    simp only [toAdd_mul, frobPow_add, Matrix.transpose_add]
    rw [← ofAdd_add]
    congr 1
    abel

omit [CharP F 2] in
theorem pow_two_pow_two_pow_eq [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (x : F) :
    (x ^ 2 ^ a) ^ 2 ^ a = x := by
  have := Fintype.ofFinite F
  rw [← pow_mul, ← pow_add, ← two_mul]
  have h := FiniteField.pow_card x
  rwa [Fintype.card_eq_nat_card, hF] at h

theorem card_hermSub_ge [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) :
    2 ^ (4 * a) ≤ Nat.card (hermSub a (Fin 2) F) := by
  have hσ := pow_two_pow_two_pow_eq hF
  have hσσ : ∀ X : Matrix (Fin 2) (Fin 2) F, frobPow a (frobPow a X) = X := by
    intro X
    ext i j
    simp [frobPow, hσ]
  have hneg : ∀ X : Matrix (Fin 2) (Fin 2) F, -X = X := by
    intro X
    ext i j
    simp only [Matrix.neg_apply]
    exact CharTwo.neg_eq _
  set f := hermTrace (F := F) a with hf
  have hker : f.ker ≤ hermSub a (Fin 2) F := by
    intro X hX
    rw [MonoidHom.mem_ker] at hX
    have h1 : Multiplicative.toAdd X + (frobPow a (Multiplicative.toAdd X))ᵀ = 0 :=
      congrArg Multiplicative.toAdd hX
    show (frobPow a (Multiplicative.toAdd X))ᵀ = Multiplicative.toAdd X
    exact (eq_neg_of_add_eq_zero_right h1).trans (hneg _)
  have hrange : f.range ≤ hermSub a (Fin 2) F := by
    rintro _ ⟨X, rfl⟩
    show (frobPow a (Multiplicative.toAdd X + (frobPow a (Multiplicative.toAdd X))ᵀ))ᵀ =
      Multiplicative.toAdd X + (frobPow a (Multiplicative.toAdd X))ᵀ
    rw [frobPow_add, frobPow_transpose, hσσ, Matrix.transpose_add, Matrix.transpose_transpose,
      add_comm]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hcard
  have hM : Nat.card (Multiplicative (Matrix (Fin 2) (Fin 2) F)) = 2 ^ (4 * a) * 2 ^ (4 * a) := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := Matrix (Fin 2) (Fin 2) F)),
      show Nat.card (Matrix (Fin 2) (Fin 2) F) = Nat.card (Fin 2 → Fin 2 → F) from rfl,
      Nat.card_fun, Nat.card_fun, Nat.card_fin, hF, ← pow_mul, ← pow_mul, ← pow_add]
    ring_nf
  rw [hM] at hcard
  have h1 := Subgroup.card_le_of_le hrange
  have h2 := Subgroup.card_le_of_le hker
  have h3 : 2 ^ (4 * a) * 2 ^ (4 * a) ≤
      Nat.card (hermSub a (Fin 2) F) * Nat.card (hermSub a (Fin 2) F) :=
    hcard.le.trans (Nat.mul_le_mul h1 h2)
  exact Nat.mul_self_le_mul_self_iff.mp h3

end CFSG.Quasithin.H13.Herm

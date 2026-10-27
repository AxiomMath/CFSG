module

public import CFSG.RankThree.PartOne.N143X.EvenSmall
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenOrthogonal

public section

namespace CFSG.RankThree.PartOne.N143X

open Matrix CFSG CFSG.Assembly.LowTwoRank

section Helpers

variable {ι : Type} [Fintype ι] {K : Type} [Field K]

theorem pairing_transpose (A J : Matrix ι ι K) (v w : ι → K) :
    (A *ᵥ v) ⬝ᵥ (J *ᵥ (A *ᵥ w)) = v ⬝ᵥ ((Aᵀ * J * A) *ᵥ w) := by
  calc (A *ᵥ v) ⬝ᵥ (J *ᵥ (A *ᵥ w)) = v ⬝ᵥ (Aᵀ *ᵥ (J *ᵥ (A *ᵥ w))) := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
    _ = v ⬝ᵥ ((Aᵀ * J * A) *ᵥ w) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]

theorem transpose_mul_eq_of_pairing [DecidableEq ι] {J A : Matrix ι ι K}
    (h : ∀ v w : ι → K, (A *ᵥ v) ⬝ᵥ (J *ᵥ (A *ᵥ w)) = v ⬝ᵥ (J *ᵥ w)) : Aᵀ * J * A = J := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [pairing_transpose] at this
  simpa using this

variable [DecidableEq ι]

@[expose] def isoQ (Q : (ι → K) → K) : Subgroup (GL ι K) where
  carrier := {A | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
  mul_mem' := fun {A B} hA hB v => by
    show Q (((A * B : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hA _).trans (hB v)
  one_mem' := fun v => by simp
  inv_mem' := fun {A} hA v => by
    show Q (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v
    have := hA (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at this
    exact this.symm

theorem statedOmega_le_isoQ (Q : (ι → K) → K) : StatedOmega Q ≤ isoQ Q := by
  have hS : Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} ≤ isoQ Q :=
    (Subgroup.closure_le _).2 fun _ h => h
  refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
  rw [commutatorElement_def]
  exact (isoQ Q).mul_mem ((isoQ Q).mul_mem ((isoQ Q).mul_mem (hS h₁) (hS h₂))
    ((isoQ Q).inv_mem (hS h₁))) ((isoQ Q).inv_mem (hS h₂))

theorem pairing_of_isoQ {Q : (ι → K) → K} {J : Matrix ι ι K}
    (hpolar : ∀ v w, Q (v + w) = Q v + Q w + v ⬝ᵥ (J *ᵥ w)) {A : GL ι K} (hA : A ∈ isoQ Q)
    (v w : ι → K) :
    ((A : Matrix ι ι K) *ᵥ v) ⬝ᵥ (J *ᵥ ((A : Matrix ι ι K) *ᵥ w)) = v ⬝ᵥ (J *ᵥ w) := by
  have h1 := hpolar ((A : Matrix ι ι K) *ᵥ v) ((A : Matrix ι ι K) *ᵥ w)
  have h2 := hpolar v w
  rw [← Matrix.mulVec_add, hA (v + w), hA v, hA w] at h1
  linear_combination h2 - h1

theorem transpose_mul_eq_of_isoQ {Q : (ι → K) → K} {J : Matrix ι ι K}
    (hpolar : ∀ v w, Q (v + w) = Q v + Q w + v ⬝ᵥ (J *ᵥ w)) {A : GL ι K} (hA : A ∈ isoQ Q) :
    (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J :=
  transpose_mul_eq_of_pairing (pairing_of_isoQ hpolar hA)

end Helpers


section Scalar

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem sq_eq_one_of_scalar_mem_isoQ {Q : (ι → K) → K} (hQ : ∀ (c : K) v, Q (c • v) = c ^ 2 * Q v)
    {v0 : ι → K} (hv0 : Q v0 = 1) {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar ι c ∈ isoQ Q) : c ^ 2 = 1 := by
  have h := hc v0
  have hv : ((Matrix.GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) *ᵥ v0 =
      (c : K) • v0 := by
    funext i
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [hv, hQ, hv0, mul_one] at h
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)

end Scalar

section Plus

variable {K : Type} [Field K]

@[expose] def plusJ (n : ℕ) (K : Type) [Field K] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 1 0

theorem plusJ_mul_self (n : ℕ) : plusJ n K * plusJ n K = 1 := by
  simp only [plusJ, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem plusJ_det_ne_zero (n : ℕ) : (plusJ n K).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (plusJ_mul_self (K := K) n)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem quadPlus_polar (n : ℕ) (v w : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n K (v + w) = StatedQuadPlus n K v + StatedQuadPlus n K w +
      v ⬝ᵥ (plusJ n K *ᵥ w) := by
  simp only [StatedQuadPlus, plusJ, Pi.add_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  simp [Matrix.one_apply, Finset.sum_add_distrib, mul_add, add_mul]
  have h : ∑ x : Fin n, w (Sum.inl x) * v (Sum.inr x) =
      ∑ x : Fin n, v (Sum.inr x) * w (Sum.inl x) := Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [h]
  ring

theorem quadPlus_smul (n : ℕ) (c : K) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n K (c • v) = c ^ 2 * StatedQuadPlus n K v := by
  simp only [StatedQuadPlus, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem quadPlus_one (n : ℕ) (hn : 1 ≤ n) :
    StatedQuadPlus n K (Pi.single (Sum.inl ⟨0, hn⟩) 1 + Pi.single (Sum.inr ⟨0, hn⟩) 1) = 1 := by
  simp [StatedQuadPlus, Pi.single_apply]

end Plus

section Minus

variable {K : Type} [Field K]

@[expose] def quadMinusJ (n : ℕ) (b : K) :
    Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K :=
  Matrix.of fun a c =>
    match a, c with
    | .inl i, .inr (.inl j) => if i = j then 1 else 0
    | .inr (.inl i), .inl j => if i = j then 1 else 0
    | .inr (.inr u), .inr (.inr w) => if u ≠ w then b else 0
    | _, _ => 0

theorem quadMinus_polar [CharP K 2] (n : ℕ) (b c : K)
    (v w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c (v + w) = StatedQuadMinus n K b c v + StatedQuadMinus n K b c w +
      v ⬝ᵥ (quadMinusJ n b *ᵥ w) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp only [StatedQuadMinus, quadMinusJ, Pi.add_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.of_apply]
  simp [Finset.sum_add_distrib, mul_add, add_mul]
  have hs : ∑ x : Fin (n - 1), w (Sum.inl x) * v (Sum.inr (Sum.inl x)) =
      ∑ x : Fin (n - 1), v (Sum.inr (Sum.inl x)) * w (Sum.inl x) :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [hs]
  linear_combination (v (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 0)) +
    c * v (Sum.inr (Sum.inr 1)) * w (Sum.inr (Sum.inr 1))) * h2

theorem quadMinus_smul (n : ℕ) (b c d : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c (d • v) = d ^ 2 * StatedQuadMinus n K b c v :=
  CFSG.QuasithinUnique.Setup.Family.quadMinus_smul n b c d v

theorem quadMinus_one (n : ℕ) (b c : K) (hn : 2 ≤ n) :
    StatedQuadMinus n K b c (Pi.single (Sum.inl ⟨0, by omega⟩) 1 +
      Pi.single (Sum.inr (Sum.inl ⟨0, by omega⟩)) 1) = 1 := by
  simp [StatedQuadMinus, Pi.single_apply]

theorem quadMinusJ_mul_self (n : ℕ) (b : K) :
    quadMinusJ n b * quadMinusJ n b = Matrix.diagonal (fun a => match a with
      | .inl _ => (1 : K) | .inr (.inl _) => 1 | .inr (.inr _) => b ^ 2) := by
  ext a c
  rcases a with i | i | u <;> rcases c with j | j | w
  all_goals
    simp [Matrix.mul_apply, Fintype.sum_sum_type, quadMinusJ, Matrix.diagonal_apply,
      Fin.sum_univ_two]
  fin_cases u <;> fin_cases w <;> simp [sq]

theorem quadMinusJ_det_ne_zero (n : ℕ) {b : K} (hb : b ≠ 0) : (quadMinusJ n b).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (quadMinusJ_mul_self n b)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_diagonal] at this
  refine (Finset.prod_ne_zero_iff.2 (fun a _ => ?_)) this.symm
  rcases a with i | i | u <;> simp [hb]

end Minus


theorem factorization_three_pomegaPlus_le {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaPlus n 2 f) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) :
    (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1 := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn4 : 4 ≤ n := hadm.2.2
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_card_two_pow hK hp (by omega)
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  refine factorization_three_le_one_of_matrix_model_form (StatedOmega (StatedQuadPlus n K)) e hp
    hp2 hpK (d := 2) ?_ ?_ (plusJ n K) (plusJ_det_ne_zero n)
    (fun g hg => transpose_mul_eq_of_isoQ (quadPlus_polar n) (statedOmega_le_isoQ _ hg)) hE
    (by simp; omega)
  · intro c hc
    exact sq_eq_one_of_scalar_mem_isoQ (quadPlus_smul n) (quadPlus_one n (by omega))
      (statedOmega_le_isoQ _ hc)
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega

theorem factorization_three_pomegaMinus_le {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaMinus n 2 f) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) :
    (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1 := by
  obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hmod
  have hn4 : 4 ≤ n := hadm.2.2
  have hchar : CharP K 2 := charP_two_of_card hK
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_card_two_pow hK hp (by omega)
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
    apply hbc s
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [hb0, hs]
    linear_combination (s * s) * h2
  refine factorization_three_le_one_of_matrix_model_form
    (StatedOmega (StatedQuadMinus n K b c)) e hp hp2 hpK (d := 2) ?_ ?_ (quadMinusJ n b)
    (quadMinusJ_det_ne_zero n hb)
    (fun g hg => transpose_mul_eq_of_isoQ (quadMinus_polar n b c) (statedOmega_le_isoQ _ hg)) hE
    (by simp; omega)
  · intro d hd
    exact sq_eq_one_of_scalar_mem_isoQ (quadMinus_smul n b c) (quadMinus_one n b c (by omega))
      (statedOmega_le_isoQ _ hd)
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega

end CFSG.RankThree.PartOne.N143X

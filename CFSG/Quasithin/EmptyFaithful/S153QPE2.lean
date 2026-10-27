module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.Quasithin.QP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {F : Type} [Field F]

theorem cube_eq_one_of_commute_torus [Fintype F] (hF : Fintype.card F = 4) {x : StatedSp 2 F}
    (hx : ∀ t : Fin 2 → Fˣ, x * torusHom t = torusHom t * x) : x ^ 3 = 1 := by
  classical
  have hcard : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [hcard])
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    omega
  have hω3 : ω ^ 3 = 1 := by
    have := pow_orderOf_eq_one ω
    rwa [hω] at this
  have hωinv : ω ≠ ω⁻¹ := by
    intro h
    have h2 : ω ^ 2 = 1 := by
      calc ω ^ 2 = ω * ω := sq ω
        _ = ω * ω⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel ω
    have h3 : orderOf ω ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hω] at h3
    omega
  have hinv1 : ω⁻¹ ≠ 1 := by
    intro h
    exact hω1 (inv_eq_one.1 h)
  set X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hX
  have hcomm : ∀ t : Fin 2 → Fˣ, X * diagonal (Sum.elim (fun i => (t i : F))
      fun i => (((t i)⁻¹ : Fˣ) : F)) = diagonal (Sum.elim (fun i => (t i : F))
      fun i => (((t i)⁻¹ : Fˣ) : F)) * X := by
    intro t
    have h := congrArg (fun g : StatedSp 2 F =>
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (hx t)
    simpa [coe_torusHom] using h
  have hentry : ∀ (t : Fin 2 → Fˣ) (i j : Fin 2 ⊕ Fin 2),
      X i j * (Sum.elim (fun k => (t k : F)) fun k => (((t k)⁻¹ : Fˣ) : F)) j =
        (Sum.elim (fun k => (t k : F)) fun k => (((t k)⁻¹ : Fˣ) : F)) i * X i j := by
    intro t i j
    have := congrFun (congrFun (hcomm t) i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hoff : ∀ i j : Fin 2 ⊕ Fin 2, i ≠ j → X i j = 0 := by
    intro i j hij
    have key : ∃ t : Fin 2 → Fˣ, (Sum.elim (fun k => (t k : F)) fun k => (((t k)⁻¹ : Fˣ) : F)) i ≠
        (Sum.elim (fun k => (t k : F)) fun k => (((t k)⁻¹ : Fˣ) : F)) j := by
      have e1 : ((ω : Fˣ) : F) ≠ 1 := fun h => hω1 (Units.ext h)
      have e2 : ((ω : Fˣ) : F) ≠ (((ω⁻¹ : Fˣ)) : F) := fun h => hωinv (Units.ext h)
      have e3 : (((ω⁻¹ : Fˣ)) : F) ≠ 1 := fun h => hinv1 (Units.ext h)
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        first
        | exact absurd rfl hij
        | exact ⟨![ω, 1], by simpa using e1⟩
        | exact ⟨![ω, 1], by simpa using e1.symm⟩
        | exact ⟨![ω, 1], by simpa using e2⟩
        | exact ⟨![ω, 1], by simpa using e2.symm⟩
        | exact ⟨![ω, 1], by simpa using e3⟩
        | exact ⟨![ω, 1], by simpa using e3.symm⟩
        | exact ⟨![1, ω], by simpa using e1⟩
        | exact ⟨![1, ω], by simpa using e1.symm⟩
        | exact ⟨![1, ω], by simpa using e2⟩
        | exact ⟨![1, ω], by simpa using e2.symm⟩
    obtain ⟨t, ht⟩ := key
    have h := hentry t i j
    have h2 : X i j * ((Sum.elim (fun k => (t k : F)) fun k => (((t k)⁻¹ : Fˣ) : F)) j -
        (Sum.elim (fun k => (t k : F)) fun k => (((t k)⁻¹ : Fˣ) : F)) i) = 0 := by
      linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.1 h3).symm ht
  have hdiag : X = diagonal (fun i => X i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hoff i j hij
  have hdet : X.det ≠ 0 := by
    have := (x : GL (Fin 2 ⊕ Fin 2) F).isUnit
    exact (Matrix.isUnit_iff_isUnit_det _).1 this |>.ne_zero
  have hne : ∀ i, X i i ≠ 0 := by
    intro i h0
    apply hdet
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using h0)
  have hcube : ∀ i, X i i ^ 3 = 1 := by
    intro i
    have := FiniteField.pow_card_sub_one_eq_one (X i i) (hne i)
    rwa [hF] at this
  have hX3 : X ^ 3 = 1 := by
    rw [hdiag, Matrix.diagonal_pow]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hcube]
    · simp [hij]
  apply Subtype.ext
  apply Units.ext
  show ((x : GL (Fin 2 ⊕ Fin 2) F) ^ 3 : GL (Fin 2 ⊕ Fin 2) F).val = 1
  rw [Units.val_pow_eq_pow_val]
  exact hX3

end CFSG.Quasithin.QP

module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.CentralCover

open Matrix
open scoped MatrixGroups

section Elements

variable {K : Type*} [Field K]

@[expose] def sl2Diag (a : Kˣ) : SL(2, K) :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [det_fin_two]⟩

@[expose] def sl2Upper (c : K) : SL(2, K) := ⟨!![1, c; 0, 1], by simp [det_fin_two]⟩

variable (K) in
@[expose] def sl2Weyl : SL(2, K) := ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

theorem coe_sl2Diag (a : Kˣ) :
    (sl2Diag a : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] := rfl

theorem coe_sl2Upper (c : K) : (sl2Upper c : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

theorem coe_sl2Weyl : (sl2Weyl K : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

theorem sl2Diag_mul (a b : Kˣ) : sl2Diag (a * b) = sl2Diag a * sl2Diag b := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag, coe_sl2Diag, coe_sl2Diag]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem sl2Diag_one : sl2Diag (1 : Kˣ) = 1 := by
  ext i j
  rw [coe_sl2Diag, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Upper_add (c d : K) : sl2Upper (c + d) = sl2Upper c * sl2Upper d := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Upper, coe_sl2Upper]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2Upper_zero : sl2Upper (0 : K) = 1 := by
  ext i j
  rw [coe_sl2Upper, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

variable (K) in
@[expose] def sl2DiagHom : Kˣ →* SL(2, K) where
  toFun := sl2Diag
  map_one' := sl2Diag_one
  map_mul' := sl2Diag_mul

variable (K) in
@[expose] def sl2UpperHom : Multiplicative K →* SL(2, K) where
  toFun c := sl2Upper (Multiplicative.toAdd c)
  map_one' := sl2Upper_zero
  map_mul' _ _ := sl2Upper_add _ _

theorem sl2DiagHom_apply (a : Kˣ) : sl2DiagHom K a = sl2Diag a := rfl

theorem sl2UpperHom_apply (c : Multiplicative K) :
    sl2UpperHom K c = sl2Upper (Multiplicative.toAdd c) := rfl

theorem sl2Diag_injective : Function.Injective (sl2Diag (K := K)) := by
  intro a b h
  apply Units.ext
  have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa [coe_sl2Diag] using this

theorem sl2Upper_injective : Function.Injective (sl2Upper (K := K)) := by
  intro a b h
  have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [coe_sl2Upper] using this

theorem sl2UpperHom_injective : Function.Injective (sl2UpperHom K) :=
  fun _ _ h => Multiplicative.toAdd.injective (sl2Upper_injective h)

theorem sl2Upper_pow (c : K) (n : ℕ) : sl2Upper c ^ n = sl2Upper (n * c) := by
  have := map_pow (sl2UpperHom K) (Multiplicative.ofAdd c) n
  rw [sl2UpperHom_apply, sl2UpperHom_apply, ← ofAdd_nsmul, toAdd_ofAdd, toAdd_ofAdd,
    nsmul_eq_mul] at this
  exact this.symm

theorem orderOf_sl2Diag (a : Kˣ) : orderOf (sl2Diag a) = orderOf a :=
  orderOf_injective (sl2DiagHom K) sl2Diag_injective a

theorem sl2Diag_mul_upper (a : Kˣ) (c : K) :
    sl2Diag a * sl2Upper c = sl2Upper ((a : K) ^ 2 * c) * sl2Diag a := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag,
    coe_sl2Upper, coe_sl2Upper]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem sl2Diag_conj_upper (a : Kˣ) (c : K) :
    sl2Diag a * sl2Upper c * (sl2Diag a)⁻¹ = sl2Upper ((a : K) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul, sl2Diag_mul_upper]

theorem sl2Weyl_conj_diag (a : Kˣ) :
    sl2Weyl K * sl2Diag a * (sl2Weyl K)⁻¹ = (sl2Diag a)⁻¹ := by
  have h : (sl2Diag a)⁻¹ = sl2Diag a⁻¹ := by
    rw [← sl2DiagHom_apply, ← sl2DiagHom_apply, map_inv]
  rw [h, mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag,
    coe_sl2Diag, coe_sl2Weyl]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Diag_neg_one_commute (g : SL(2, K)) : Commute (sl2Diag (-1)) g := by
  have h : (sl2Diag (-1 : Kˣ) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    rw [coe_sl2Diag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Commute, SemiconjBy]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h]
  simp

theorem orderOf_sl2Diag_neg_one (hK : ringChar K ≠ 2) : orderOf (sl2Diag (-1 : Kˣ)) = 2 := by
  rw [orderOf_sl2Diag, ← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one]
  simp [hK]

end Elements

section Inverted

variable {K : Type*} [Field K] [Fintype K]

theorem exists_inverted_of_dvd_card_sub_one {p : ℕ} (hp : p.Prime) (hpq : p ∣ Fintype.card K - 1) :
    ∃ h w : SL(2, K), orderOf h = p ∧ w * h * w⁻¹ = h⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact hpq
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hcard
  exact ⟨sl2Diag ζ, sl2Weyl K, by rw [orderOf_sl2Diag, hζ], sl2Weyl_conj_diag ζ⟩

end Inverted

section Nonsplit

variable {K : Type*} [Field K]

@[expose] def torusMat (ε a b : K) : Matrix (Fin 2) (Fin 2) K := !![a, ε * b; b, a]

theorem torusMat_mul (ε a b c d : K) :
    torusMat ε a b * torusMat ε c d = torusMat ε (a * c + ε * b * d) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torusMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_torusMat (ε a b : K) : (torusMat ε a b).det = a ^ 2 - ε * b ^ 2 := by
  simp [torusMat, Matrix.det_fin_two]
  ring

theorem torusMat_one (ε : K) : torusMat ε 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torusMat]

theorem torusMat_zero_zero (ε a b : K) : torusMat ε a b 0 0 = a := rfl

theorem torusMat_one_zero (ε a b : K) : torusMat ε a b 1 0 = b := rfl

theorem sq_sub_mul_sq_ne_zero {ε : K} (hε : ¬ IsSquare ε) {a b : K} (hab : (a, b) ≠ 0) :
    a ^ 2 - ε * b ^ 2 ≠ 0 := by
  intro h
  by_cases hb : b = 0
  · rw [hb] at h hab
    have ha : a = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 (by simpa using h)
    exact hab (by rw [ha]; rfl)
  · apply hε
    refine ⟨a / b, ?_⟩
    field_simp
    linear_combination -h

@[expose] def torusUnits (ε : K) : Subgroup (GL (Fin 2) K) where
  carrier := {g | ∃ a b : K, (g : Matrix (Fin 2) (Fin 2) K) = torusMat ε a b}
  mul_mem' := by
    rintro g g' ⟨a, b, hg⟩ ⟨c, d, hg'⟩
    exact ⟨_, _, by rw [Units.val_mul, hg, hg', torusMat_mul]⟩
  one_mem' := ⟨1, 0, by rw [Units.val_one, torusMat_one]⟩
  inv_mem' := by
    rintro g ⟨a, b, hg⟩
    have hdet : a ^ 2 - ε * b ^ 2 ≠ 0 := by
      rw [← det_torusMat, ← hg]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    refine ⟨a / (a ^ 2 - ε * b ^ 2), -b / (a ^ 2 - ε * b ^ 2), ?_⟩
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hg, torusMat_mul, ← torusMat_one ε]
    congr 1
    · field_simp
      ring
    · field_simp
      ring

theorem card_torusUnits [Fintype K] [DecidableEq K] {ε : K} (hε : ¬ IsSquare ε) :
    Nat.card (torusUnits ε) = Fintype.card K ^ 2 - 1 := by
  classical
  have hunit : ∀ v : {v : K × K // v ≠ 0}, IsUnit (torusMat ε v.1.1 v.1.2).det := fun v => by
    rw [det_torusMat]
    exact (sq_sub_mul_sq_ne_zero hε v.2).isUnit
  let e : torusUnits ε ≃ {v : K × K // v ≠ 0} :=
    { toFun := fun g => ⟨(((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0,
          ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0), by
        obtain ⟨a, b, hg⟩ := g.2
        intro h0
        have h1 : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
          ((Matrix.isUnit_iff_isUnit_det _).1 (g : GL (Fin 2) K).isUnit).ne_zero
        rw [hg, det_torusMat] at h1
        rw [hg, torusMat_zero_zero, torusMat_one_zero] at h0
        apply h1
        rw [(Prod.mk_eq_zero.1 h0).1, (Prod.mk_eq_zero.1 h0).2]
        ring⟩
      invFun := fun v => ⟨Matrix.nonsingInvUnit _ (hunit v), v.1.1, v.1.2, rfl⟩
      left_inv := fun g => by
        obtain ⟨a, b, hg⟩ := g.2
        apply Subtype.ext
        apply Units.ext
        change torusMat ε (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0)
          (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) =
          ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        rw [hg]
        rfl
      right_inv := fun v => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_prod,
    Fintype.card_subtype_eq, sq]

theorem exists_inverted_of_dvd_card_add_one [Fintype K] (hK : ringChar K ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Fintype.card K + 1) :
    ∃ h w : SL(2, K), orderOf h = p ∧ w * h * w⁻¹ = h⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ε, hε⟩ := FiniteField.exists_nonsquare hK
  set q := Fintype.card K with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hdvd : p ∣ Nat.card (torusUnits ε) := by
    rw [card_torusUnits hε]
    have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      cases q with
      | zero => omega
      | succ n => simp [sq]; ring_nf; omega
    rw [hfac]
    exact Dvd.dvd.mul_left hpq _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨a, b, hab⟩ := g.2
  have hdet : a ^ 2 - ε * b ^ 2 = 1 := by
    have hd0 : a ^ 2 - ε * b ^ 2 ≠ 0 := by
      rw [← det_torusMat, ← hab]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (g : GL (Fin 2) K).isUnit).ne_zero
    have hgp : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ p = 1 := by
      have h1 : g ^ p = 1 := by rw [← hg, pow_orderOf_eq_one]
      have h2 := congrArg (fun x : torusUnits ε => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
        h1
      simpa using h2
    have hdp : (a ^ 2 - ε * b ^ 2) ^ p = 1 := by
      have := congrArg Matrix.det hgp
      rwa [Matrix.det_pow, hab, det_torusMat, Matrix.det_one] at this
    have hdq : (a ^ 2 - ε * b ^ 2) ^ (q - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ hd0
    have hcop : Nat.Coprime p (q - 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hpq'
      have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hpq hpq'
      have h3 : (q + 1) - (q - 1) = 2 := by omega
      rw [h3] at h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hdp) (orderOf_dvd_of_pow_eq_one hdq))
  let h₀ : SL(2, K) := ⟨torusMat ε a b, by rw [det_torusMat, hdet]⟩
  have hh₀ : Matrix.SpecialLinearGroup.toGL h₀ = (g : GL (Fin 2) K) := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hab]
  have hord : orderOf h₀ = p := by
    rw [← orderOf_injective _ Matrix.SpecialLinearGroup.toGL_injective h₀, hh₀,
      Subgroup.orderOf_coe, hg]
  have hodd : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two hK
  have hε0 : ε ≠ 0 := fun h0 => hε (h0 ▸ ⟨0, by ring⟩)
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2) (g := Polynomial.C (-ε) * Polynomial.X ^ 2 + Polynomial.C 1)
    (by compute_degree!) (by compute_degree!) hodd
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at hxy
  let w₀ : SL(2, K) := ⟨!![x, -(ε * y); y, -x], by
    rw [Matrix.det_fin_two_of]
    linear_combination -hxy⟩
  refine ⟨h₀, w₀, hord, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  change (!![x, -(ε * y); y, -x] * torusMat ε a b) i j =
    ((!![torusMat ε a b 1 1, -torusMat ε a b 0 1; -torusMat ε a b 1 0, torusMat ε a b 0 0] :
      Matrix (Fin 2) (Fin 2) K) * !![x, -(ε * y); y, -x]) i j
  fin_cases i <;> fin_cases j <;> simp [torusMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end Nonsplit

section Dichotomy

variable {K : Type*} [Field K] [Fintype K]

theorem exists_inverted_of_dvd_card_sq_sub_one (hK : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Fintype.card K ^ 2 - 1) :
    ∃ h w : SL(2, K), orderOf h = p ∧ w * h * w⁻¹ = h⁻¹ := by
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  have hfac : Fintype.card K ^ 2 - 1 = (Fintype.card K - 1) * (Fintype.card K + 1) := by
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card K = n + 1 := ⟨Fintype.card K - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel, sq]
    ring_nf
    omega
  rw [hfac] at hpq
  rcases (Nat.Prime.dvd_mul hp).1 hpq with h | h
  · exact exists_inverted_of_dvd_card_sub_one hp h
  · exact exists_inverted_of_dvd_card_add_one hK hp hp2 h

end Dichotomy

end CFSG.RankThree.CentralCover

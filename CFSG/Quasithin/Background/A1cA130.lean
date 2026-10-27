module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Choose.Dvd


public section

namespace CFSG.Quasithin

open Matrix
open scoped MatrixGroups

namespace A1c

theorem sq_eq_zero_of_pow_eq_zero_fin_two {F : Type*} [CommRing F] [IsDomain F]
    {N : Matrix (Fin 2) (Fin 2) F} {n : ℕ} (hn : 0 < n) (h : N ^ n = 0) : N ^ 2 = 0 := by
  have hdet : N.det = 0 := by
    have := congrArg Matrix.det h
    rw [Matrix.det_pow, Matrix.det_zero] at this
    exact pow_eq_zero_iff (by omega) |>.1 this
  have hCH : N ^ 2 = N.trace • N := by
    have := Matrix.aeval_self_charpoly N
    rw [Matrix.charpoly_fin_two] at this
    simp [hdet] at this
    rw [← Algebra.smul_def] at this
    exact sub_eq_zero.1 this
  have hpow : ∀ k : ℕ, N ^ (k + 1) = N.trace ^ k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, smul_mul_assoc, ← pow_two, hCH, smul_smul, ← pow_succ]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hpow] at h
  by_cases hN0 : N = 0
  · rw [pow_two, hN0, zero_mul]
  · obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hN0 (Matrix.ext fun i j => hcon i j)
    have h1 : N.trace ^ m * N i j = 0 := by
      have := congrFun (congrFun h i) j
      simpa using this
    have h2 : N.trace ^ m = 0 := (mul_eq_zero.1 h1).resolve_right hij
    rw [hCH, pow_eq_zero_iff'.1 h2 |>.1, zero_smul]

theorem exists_eq_mul_of_castHom_eq_zero {p : ℕ} [Fact p.Prime] {z : ZMod (p ^ 2)}
    (h : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) z = 0) :
    ∃ w : ZMod (p ^ 2), z = (p : ZMod (p ^ 2)) * w := by
  have h1 : (z.val : ZMod p) = 0 := by
    rw [← map_natCast (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)), ZMod.natCast_zmod_val]
    exact h
  obtain ⟨k, hk⟩ := (CharP.cast_eq_zero_iff (ZMod p) p z.val).1 h1
  refine ⟨(k : ZMod (p ^ 2)), ?_⟩
  rw [← Nat.cast_mul, ← hk, ZMod.natCast_zmod_val]

theorem exists_eq_mul_of_mul_eq_zero {p : ℕ} [Fact p.Prime] {z : ZMod (p ^ 2)}
    (h : (p : ZMod (p ^ 2)) * z = 0) : ∃ w : ZMod (p ^ 2), z = (p : ZMod (p ^ 2)) * w := by
  have h1 : ((p * z.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact h
  have h2 : p ^ 2 ∣ p * z.val := (CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2) _).1 h1
  have h3 : p ∣ z.val := by
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos (by rw [hc]; ring)⟩
  obtain ⟨k, hk⟩ := h3
  exact ⟨(k : ZMod (p ^ 2)), by rw [← Nat.cast_mul, ← hk, ZMod.natCast_zmod_val]⟩

theorem matrix_pow_eq_one_imp_smul_sub_one_eq_zero {p : ℕ} [hp : Fact p.Prime] (hp4 : 3 < p)
    {M : Matrix (Fin 2) (Fin 2) (ZMod (p ^ 2))} (hM : M ^ p = 1) :
    (p : ZMod (p ^ 2)) • (M - 1) = 0 := by
  set N : Matrix (Fin 2) (Fin 2) (ZMod (p ^ 2)) := M - 1 with hN
  have hMN : M = 1 + N := by rw [hN]; abel
  let φ : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
  have hbar : (φ.mapMatrix N) ^ p = 0 := by
    have h1 : (φ.mapMatrix M) ^ p = 1 := by rw [← map_pow, hM, map_one]
    have h2 : φ.mapMatrix M = 1 + φ.mapMatrix N := by rw [hMN, map_add, map_one]
    rw [h2] at h1
    have h3 := add_pow_char_of_commute p (Commute.one_left (φ.mapMatrix N))
    rw [h3, one_pow] at h1
    simpa using h1
  have hsq : (φ.mapMatrix N) ^ 2 = 0 := sq_eq_zero_of_pow_eq_zero_fin_two hp.out.pos hbar
  have hdiv : ∀ i j, ∃ w : ZMod (p ^ 2), (N ^ 2) i j = (p : ZMod (p ^ 2)) * w := by
    intro i j
    have h0 : φ.mapMatrix (N ^ 2) = 0 := by rw [map_pow]; exact hsq
    have h1 : φ ((N ^ 2) i j) = 0 := congrFun (congrFun h0 i) j
    exact exists_eq_mul_of_castHom_eq_zero h1
  choose A hA using hdiv
  have hN2 : N ^ 2 = (p : ZMod (p ^ 2)) • (Matrix.of A) := by
    ext i j
    simp [hA i j]
  have hp2 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
    rw [← Nat.cast_mul, ← sq]; exact ZMod.natCast_self _
  have hpN2 : (p : ZMod (p ^ 2)) • N ^ 2 = 0 := by rw [hN2, smul_smul, hp2, zero_smul]
  have hN4 : N ^ 4 = 0 := by
    have : N ^ 4 = N ^ 2 * N ^ 2 := by rw [← pow_add]
    rw [this, hN2, smul_mul_assoc, mul_smul_comm, smul_smul, hp2, zero_smul]
  have hpN2' : p • N ^ 2 = 0 := by rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ 2))]; exact hpN2
  have hbin : (N + 1) ^ p = 1 + (p : ZMod (p ^ 2)) • N := by
    rw [(Commute.one_right N).add_pow]
    have hsub : Finset.range 2 ⊆ Finset.range (p + 1) := Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub ?_]
    · simp [Finset.sum_range_succ, Nat.cast_smul_eq_nsmul]
      exact (Nat.cast_comm p N).symm
    · intro m hm hm2
      rw [Finset.mem_range] at hm hm2
      rw [one_pow, mul_one]
      rcases Nat.lt_or_ge m p with hlt | hge
      · obtain ⟨c, hc⟩ := hp.out.dvd_choose_self (by omega : m ≠ 0) hlt
        have e1 : N ^ m * ((p.choose m : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ 2))) =
            (p.choose m) • N ^ m := by
          rw [← Nat.cast_comm, nsmul_eq_mul]
        have e2 : N ^ m = N ^ 2 * N ^ (m - 2) := by
          rw [← pow_add]; congr 1; omega
        rw [e1, hc, mul_comm p c, mul_smul, e2, ← smul_mul_assoc, hpN2', zero_mul, smul_zero]
      · have hmp : m = p := by omega
        have e3 : N ^ p = N ^ 4 * N ^ (p - 4) := by
          rw [← pow_add]; congr 1; omega
        rw [hmp, e3, hN4, zero_mul, zero_mul]
  have h1 : (N + 1) ^ p = 1 := by rw [add_comm, ← hMN]; exact hM
  simpa using h1.symm.trans hbin

@[expose] noncomputable def autLin (p : ℕ) (α : MulAut (Multiplicative (Fin 2 → ZMod (p ^ 2)))) :
    Module.End (ZMod (p ^ 2)) (Fin 2 → ZMod (p ^ 2)) :=
  (AddMonoidHom.toMultiplicative.symm α.toMonoidHom).toZModLinearMap (p ^ 2)

theorem autLin_apply (p : ℕ) (α : MulAut (Multiplicative (Fin 2 → ZMod (p ^ 2))))
    (v : Fin 2 → ZMod (p ^ 2)) :
    autLin p α v = Multiplicative.toAdd (α (Multiplicative.ofAdd v)) := rfl

@[expose] noncomputable def autLinHom (p : ℕ) :
    MulAut (Multiplicative (Fin 2 → ZMod (p ^ 2))) →*
      Module.End (ZMod (p ^ 2)) (Fin 2 → ZMod (p ^ 2)) where
  toFun := autLin p
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' := fun _ _ => LinearMap.ext fun _ => rfl

theorem fixes_of_orderOf_eq_prime {p : ℕ} [hp : Fact p.Prime] (hp4 : 3 < p)
    {α : MulAut (Multiplicative (Fin 2 → ZMod (p ^ 2)))} (hα : orderOf α = p)
    {x : Multiplicative (Fin 2 → ZMod (p ^ 2))} (hx : x ^ p = 1) : α x = x := by
  have hαp : α ^ p = 1 := by
    have := pow_orderOf_eq_one α
    rwa [hα] at this
  set L := autLinHom p α with hL
  have hLp : L ^ p = 1 := by rw [hL, ← map_pow, hαp, map_one]
  have hMp : (LinearMap.toMatrixAlgEquiv' L) ^ p = 1 := by rw [← map_pow, hLp, map_one]
  have h0 := matrix_pow_eq_one_imp_smul_sub_one_eq_zero hp4 hMp
  have h1 : (p : ZMod (p ^ 2)) • (L - 1) = 0 := by
    apply (LinearMap.toMatrixAlgEquiv' (R := ZMod (p ^ 2)) (n := Fin 2)).injective
    rw [map_smul, map_sub, map_one, map_zero]
    exact h0
  set v : Fin 2 → ZMod (p ^ 2) := Multiplicative.toAdd x with hvdef
  have hv : ∀ i, (p : ZMod (p ^ 2)) * v i = 0 := by
    intro i
    have := congrFun (congrArg Multiplicative.toAdd hx) i
    simpa [toAdd_pow, hvdef] using this
  choose w hw using fun i => exists_eq_mul_of_mul_eq_zero (hv i)
  have hvw : v = (p : ZMod (p ^ 2)) • w := by
    funext i; simp [hw i]
  have h2 : (p : ZMod (p ^ 2)) • (L w - w) = 0 := by
    have := LinearMap.congr_fun h1 w
    simpa using this
  have h3 : L v = v := by
    rw [hvw, map_smul]
    have h5 : (p : ZMod (p ^ 2)) • L w = (p : ZMod (p ^ 2)) • w := by
      have h6 := h2
      rw [smul_sub, sub_eq_zero] at h6
      exact h6
    rw [h5]
  have h4 : α x = Multiplicative.ofAdd (L v) := rfl
  rw [h4, h3]
  rfl

section SL2

variable (p : ℕ)

@[expose] def sl2U : SL(2, ZMod p) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2L : SL(2, ZMod p) := ⟨!![1, 0; -1, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2W : SL(2, ZMod p) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2NegOne : SL(2, ZMod p) :=
  ⟨!![-1, 0; 0, -1], by rw [Matrix.det_fin_two_of]; ring⟩

variable {p}

theorem sl2U_pow (n : ℕ) :
    ((sl2U p ^ n : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![1, (n : ZMod p); 0, 1] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2U, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2L_pow (n : ℕ) :
    ((sl2L p ^ n : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![1, 0; -(n : ZMod p), 1] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2L, Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem sl2_ULU : sl2U p * sl2L p * sl2U p = sl2W p := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [sl2U, sl2L, sl2W]
  simp

theorem sl2W_mul_self : sl2W p * sl2W p = sl2NegOne p := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp only [sl2W, sl2NegOne]
  simp

theorem sl2NegOne_mul_self : sl2NegOne p * sl2NegOne p = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp only [sl2NegOne]
  simp [Matrix.one_fin_two]

variable [hp : Fact p.Prime]

theorem orderOf_sl2U : orderOf (sl2U p) = p := by
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [sl2U_pow]
    simp [Matrix.one_fin_two]
  · intro h
    have := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
    simp [sl2U] at this

theorem orderOf_sl2L : orderOf (sl2L p) = p := by
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [sl2L_pow]
    simp [Matrix.one_fin_two]
  · intro h
    have := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0) h
    simp [sl2L] at this

theorem sl2NegOne_ne_one (hp2 : p ≠ 2) : sl2NegOne p ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simp [sl2NegOne] at this
  have h2 := (neg_one_eq_one_iff (R := ZMod p)).1 this
  rw [ZMod.ringChar_zmod_n] at h2
  exact hp2 h2

end SL2

section NoSL2

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem pow_sq_eq_one (x : Multiplicative (Fin 2 → ZMod (p ^ 2))) : x ^ (p ^ 2) = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rfl

theorem not_injective_sl2 (hp4 : 3 < p)
    (f : SL(2, ZMod p) →* MulAut (Multiplicative (Fin 2 → ZMod (p ^ 2)))) :
    ¬ Function.Injective f := by
  intro hf
  have hp2 : p ≠ 2 := by omega
  have hfix : ∀ g : SL(2, ZMod p), orderOf g = p →
      ∀ x : Multiplicative (Fin 2 → ZMod (p ^ 2)), x ^ p = 1 → f g x = x :=
    fun g hg x hx => fixes_of_orderOf_eq_prime hp4 ((orderOf_injective f hf g).trans hg) hx
  have hmul : ∀ g h : SL(2, ZMod p),
      (∀ x : Multiplicative (Fin 2 → ZMod (p ^ 2)), x ^ p = 1 → f g x = x) →
      (∀ x : Multiplicative (Fin 2 → ZMod (p ^ 2)), x ^ p = 1 → f h x = x) →
      ∀ x : Multiplicative (Fin 2 → ZMod (p ^ 2)), x ^ p = 1 → f (g * h) x = x := by
    intro g h hg hh x hx
    rw [map_mul, MulAut.mul_apply, hh x hx, hg x hx]
  have hW : ∀ x : Multiplicative (Fin 2 → ZMod (p ^ 2)), x ^ p = 1 → f (sl2W p) x = x := by
    rw [← sl2_ULU]
    exact hmul _ _ (hmul _ _ (hfix _ orderOf_sl2U) (hfix _ orderOf_sl2L)) (hfix _ orderOf_sl2U)
  have hN : ∀ x : Multiplicative (Fin 2 → ZMod (p ^ 2)), x ^ p = 1 → f (sl2NegOne p) x = x := by
    rw [← sl2W_mul_self]
    exact hmul _ _ hW hW
  set β := f (sl2NegOne p) with hβ
  have hβ2 : ∀ x, β (β x) = x := by
    intro x
    have : β * β = 1 := by rw [hβ, ← map_mul, sl2NegOne_mul_self, map_one]
    have h2 := congrArg (fun γ : MulAut (Multiplicative (Fin 2 → ZMod (p ^ 2))) => γ x) this
    simpa using h2
  have hβ1 : β = 1 := by
    ext x
    set u := β x * x⁻¹ with hu
    have hxp : (x ^ p) ^ p = 1 := by rw [← pow_mul, ← sq]; exact pow_sq_eq_one x
    have hup : u ^ p = 1 := by
      rw [hu, mul_pow, inv_pow, ← map_pow, hN (x ^ p) hxp, mul_inv_cancel]
    have hβu : β u = u := hN u hup
    have hux : β x = u * x := by rw [hu]; group
    have hu2 : u * u = 1 := by
      have h1 := hβ2 x
      rw [hux, map_mul, hβu, hux] at h1
      have h2 : u * (u * x) = 1 * x := by rw [h1, one_mul]
      rw [← mul_assoc] at h2
      exact mul_right_cancel h2
    have hu1 : u = 1 := by
      have h2d : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two u]; exact hu2)
      have hpd : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hup
      have hg : orderOf u ∣ Nat.gcd 2 p := Nat.dvd_gcd h2d hpd
      have hcop : Nat.gcd 2 p = 1 :=
        (Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)
      rw [hcop] at hg
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)
    rw [hux, hu1, one_mul]
    rfl
  exact sl2NegOne_ne_one hp2 (hf (hβ1.trans (map_one f).symm))

end NoSL2

end A1c

section A130

variable {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]

theorem fixes_of_orderOf_eq_prime_of_mulEquiv
    (hP : Nonempty (P ≃* Multiplicative (Fin 2 → ZMod (p ^ 2)))) (hp4 : 3 < p) {α : MulAut P}
    (hα : orderOf α = p) {x : P} (hx : x ^ p = 1) : α x = x := by
  obtain ⟨e⟩ := hP
  have h := A1c.fixes_of_orderOf_eq_prime hp4 (α := MulAut.congr e α)
    (by rw [MulEquiv.orderOf_eq]; exact hα) (x := e x) (by rw [← map_pow, hx, map_one])
  rw [MulAut.congr_apply] at h
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
  exact e.injective h

theorem not_injective_sl2_of_mulEquiv
    (hP : Nonempty (P ≃* Multiplicative (Fin 2 → ZMod (p ^ 2)))) (hp4 : 3 < p)
    (f : SL(2, ZMod p) →* MulAut P) : ¬ Function.Injective f := by
  obtain ⟨e⟩ := hP
  intro hf
  exact A1c.not_injective_sl2 hp4 ((MulAut.congr e).toMonoidHom.comp f)
    ((MulAut.congr e).injective.comp hf)

theorem not_exists_subgroup_mulEquiv_sl2
    (hP : Nonempty (P ≃* Multiplicative (Fin 2 → ZMod (p ^ 2)))) (hp4 : 3 < p) :
    ¬ ∃ H : Subgroup (MulAut P), Nonempty (H ≃* SL(2, ZMod p)) := by
  rintro ⟨H, ⟨φ⟩⟩
  exact not_injective_sl2_of_mulEquiv hP hp4 (H.subtype.comp φ.symm.toMonoidHom)
    (H.subtype_injective.comp φ.symm.injective)

end A130

end CFSG.Quasithin

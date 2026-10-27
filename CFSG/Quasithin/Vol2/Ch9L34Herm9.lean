module

public import CFSG.Fischer.F4
public import CFSG.Quasithin.Background.HMathieuBits
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.H13.Ch9.Herm9

open CFSG.Fischer Matrix CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

@[expose] def cj (x : F4) : F4 := x * x

@[expose] def lo (x : F4) : ZMod 2 := (x.code.val % 2 : ℕ)

@[expose] def hi (x : F4) : ZMod 2 := (x.code.val / 2 : ℕ)

@[expose] def mk (a b : ZMod 2) : F4 := ⟨⟨a.val + 2 * b.val, by
  have ha := a.val_lt
  have hb := b.val_lt
  omega⟩⟩

theorem mk_add_mk (a b : Fin 4) : (⟨a⟩ : F4) + ⟨b⟩ = ⟨a ^^^ b⟩ := by
  rw [F4.add_def]
  rfl

theorem mk_mul_mk (a b : Fin 4) : (⟨a⟩ : F4) * ⟨b⟩ = ⟨F4.mulCode a b⟩ := by
  rw [F4.mul_def]
  rfl

theorem zero_eq : (0 : F4) = ⟨0⟩ := rfl

theorem one_eq : (1 : F4) = ⟨1⟩ := rfl

theorem cj_add (x y : F4) : cj (x + y) = cj x + cj y := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  simp only [cj, mk_add_mk, mk_mul_mk, F4.mk.injEq]
  revert a b
  decide

theorem cj_mul (x y : F4) : cj (x * y) = cj x * cj y := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  simp only [cj, mk_mul_mk, F4.mk.injEq]
  revert a b
  decide

theorem cj_cj (x : F4) : cj (cj x) = x := by
  obtain ⟨a⟩ := x
  simp only [cj, mk_mul_mk, F4.mk.injEq]
  revert a
  decide

theorem cj_zero : cj 0 = 0 := by
  simp only [cj, zero_eq, mk_mul_mk, F4.mk.injEq]
  decide

theorem cj_one : cj 1 = 1 := by
  simp only [cj, one_eq, mk_mul_mk, F4.mk.injEq]
  decide

theorem lo_add (x y : F4) : lo (x + y) = lo x + lo y := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  simp only [lo, mk_add_mk]
  revert a b
  decide

theorem hi_add (x y : F4) : hi (x + y) = hi x + hi y := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  simp only [hi, mk_add_mk]
  revert a b
  decide

theorem mk_lo_hi (x : F4) : mk (lo x) (hi x) = x := by
  obtain ⟨a⟩ := x
  simp only [mk, lo, hi, F4.mk.injEq]
  revert a
  decide

theorem lo_mk (a b : ZMod 2) : lo (mk a b) = a := by
  simp only [lo, mk]
  revert a b
  decide

theorem hi_mk (a b : ZMod 2) : hi (mk a b) = b := by
  simp only [hi, mk]
  revert a b
  decide

theorem mk_add (a b c d : ZMod 2) : mk (a + c) (b + d) = mk a b + mk c d := by
  simp only [mk, mk_add_mk, F4.mk.injEq]
  revert a b c d
  decide

theorem mk_add_zero (a c : ZMod 2) : mk (a + c) 0 = mk a 0 + mk c 0 := by
  rw [← mk_add, add_zero]

theorem mk_lo_of_cj (x : F4) (h : cj x = x) : mk (lo x) 0 = x := by
  obtain ⟨a⟩ := x
  simp only [cj, mk_mul_mk, F4.mk.injEq] at h
  simp only [mk, lo, F4.mk.injEq]
  revert a
  decide

theorem cj_mk_zero (a : ZMod 2) : cj (mk a 0) = mk a 0 := by
  simp only [cj, mk, mk_mul_mk, F4.mk.injEq]
  revert a
  decide

@[expose] def cjRing : F4 ≃+* F4 where
  toFun := cj
  invFun := cj
  left_inv := cj_cj
  right_inv := cj_cj
  map_mul' := cj_mul
  map_add' := cj_add

theorem cjRing_apply (x : F4) : cjRing x = cj x := rfl

@[expose] def maskOf : (n : ℕ) → (Fin n → ZMod 2) → ℕ
  | 0, _ => 0
  | n + 1, v => (v 0).val + 2 * maskOf n fun i => v i.succ

theorem maskOf_lt : ∀ (n : ℕ) (v : Fin n → ZMod 2), maskOf n v < 2 ^ n
  | 0, _ => by simp [maskOf]
  | n + 1, v => by
    have h0 := (v 0).val_lt
    have ih := maskOf_lt n fun i => v i.succ
    rw [maskOf, pow_succ]
    omega

private theorem zmod_two_val (a : ZMod 2) (b : Bool) (h : b = decide (a.val % 2 = 1)) :
    (if b then 1 else 0 : ZMod 2) = a := by
  subst h
  revert a
  decide

theorem bvec_maskOf : ∀ (n : ℕ) (v : Fin n → ZMod 2), bvec n (maskOf n v) = v
  | 0, v => funext fun i => i.elim0
  | n + 1, v => by
    funext i
    have h0 := (v 0).val_lt
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [bvec_apply, Fin.val_zero, Nat.testBit_zero, maskOf]
      refine zmod_two_val _ _ ?_
      rw [Nat.add_mul_mod_self_left]
    · have ih := congrFun (bvec_maskOf n fun i => v i.succ) j
      rw [bvec_apply] at ih
      rw [bvec_apply, Fin.val_succ, Nat.testBit_succ, maskOf]
      have e : ((v 0).val + 2 * maskOf n fun i => v i.succ) / 2 = maskOf n fun i => v i.succ := by
        omega
      rw [e]
      exact ih

theorem maskOf_bvec {n m : ℕ} (hm : m < 2 ^ n) : maskOf n (bvec n m) = m :=
  bvec_inj (maskOf_lt n _) hm (bvec_maskOf n _)

theorem maskOf_add (n : ℕ) (v w : Fin n → ZMod 2) :
    maskOf n (v + w) = maskOf n v ^^^ maskOf n w := by
  refine bvec_inj (maskOf_lt n _) (Nat.xor_lt_two_pow (maskOf_lt n _) (maskOf_lt n _)) ?_
  rw [bvec_xor, bvec_maskOf, bvec_maskOf, bvec_maskOf]

@[expose] def dgE (a : ZMod 2) : F4 := mk a 0

@[expose] def hermV (v : Fin 9 → ZMod 2) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of ![![dgE (v 0), mk (v 3) (v 4), mk (v 5) (v 6)],
    ![cj (mk (v 3) (v 4)), dgE (v 1), mk (v 7) (v 8)],
    ![cj (mk (v 5) (v 6)), cj (mk (v 7) (v 8)), dgE (v 2)]]

@[expose] def codeV (Y : Matrix (Fin 3) (Fin 3) F4) : Fin 9 → ZMod 2 :=
  ![lo (Y 0 0), lo (Y 1 1), lo (Y 2 2), lo (Y 0 1), hi (Y 0 1), lo (Y 0 2), hi (Y 0 2),
    lo (Y 1 2), hi (Y 1 2)]

@[expose] def herm (m : Fin 512) : Matrix (Fin 3) (Fin 3) F4 := hermV (bvec 9 m)

@[expose] def code (Y : Matrix (Fin 3) (Fin 3) F4) : Fin 512 :=
  ⟨maskOf 9 (codeV Y), maskOf_lt 9 _⟩

@[expose] def IsHerm (Y : Matrix (Fin 3) (Fin 3) F4) : Prop := ∀ i j, Y j i = cj (Y i j)

@[expose] def bar (Y : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4 := Y.map cj

theorem bar_apply (Y : Matrix (Fin 3) (Fin 3) F4) (i j : Fin 3) : bar Y i j = cj (Y i j) := rfl

theorem bar_bar (Y : Matrix (Fin 3) (Fin 3) F4) : bar (bar Y) = Y := by
  ext i j
  exact cj_cj _

theorem bar_mul (Y Z : Matrix (Fin 3) (Fin 3) F4) : bar (Y * Z) = bar Y * bar Z :=
  Matrix.map_mul (f := (cjRing : F4 →+* F4))

theorem bar_add (Y Z : Matrix (Fin 3) (Fin 3) F4) : bar (Y + Z) = bar Y + bar Z := by
  ext i j
  exact cj_add _ _

theorem bar_one : bar (1 : Matrix (Fin 3) (Fin 3) F4) = 1 := by
  ext i j
  rw [bar_apply, one_apply]
  split_ifs
  · exact cj_one
  · exact cj_zero

theorem bar_transpose (Y : Matrix (Fin 3) (Fin 3) F4) : bar Yᵀ = (bar Y)ᵀ := rfl

theorem codeV_hermV (v : Fin 9 → ZMod 2) : codeV (hermV v) = v := by
  funext i
  fin_cases i <;> simp [codeV, hermV, dgE, lo_mk, hi_mk]

theorem code_herm (m : Fin 512) : code (herm m) = m := by
  apply Fin.ext
  show maskOf 9 (codeV (hermV (bvec 9 m))) = m
  rw [codeV_hermV]
  exact maskOf_bvec m.2

theorem isHerm_hermV (v : Fin 9 → ZMod 2) : IsHerm (hermV v) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hermV, dgE, cj_cj, cj_mk_zero]

theorem isHerm_herm (m : Fin 512) : IsHerm (herm m) := isHerm_hermV _

theorem hermV_codeV {Y : Matrix (Fin 3) (Fin 3) F4} (hY : IsHerm Y) : hermV (codeV Y) = Y := by
  have hd : ∀ i, dgE (lo (Y i i)) = Y i i := fun i => mk_lo_of_cj _ (hY i i).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermV, codeV, mk_lo_hi, hd, (hY 0 1).symm, (hY 0 2).symm, (hY 1 2).symm]

theorem herm_code {Y : Matrix (Fin 3) (Fin 3) F4} (hY : IsHerm Y) : herm (code Y) = Y := by
  show hermV (bvec 9 (maskOf 9 (codeV Y))) = Y
  rw [bvec_maskOf, hermV_codeV hY]

theorem hermV_add (v w : Fin 9 → ZMod 2) : hermV (v + w) = hermV v + hermV w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermV, dgE, mk_add, mk_add_zero, cj_add]

theorem codeV_add (Y Z : Matrix (Fin 3) (Fin 3) F4) : codeV (Y + Z) = codeV Y + codeV Z := by
  funext i
  fin_cases i <;> simp [codeV, lo_add, hi_add]

theorem bvec_val (m : Fin 512) (m' : Fin 512) :
    bvec 9 ((m ^^^ m' : Fin 512) : ℕ) = bvec 9 m + bvec 9 m' := by
  rw [← bvec_xor]
  congr 1
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 9) m.2 m'.2)

theorem herm_xor (m m' : Fin 512) : herm (m ^^^ m') = herm m + herm m' := by
  rw [herm, bvec_val, hermV_add]
  rfl

theorem code_add (Y Z : Matrix (Fin 3) (Fin 3) F4) : code (Y + Z) = code Y ^^^ code Z := by
  apply Fin.ext
  show maskOf 9 (codeV (Y + Z)) = (maskOf 9 (codeV Y) ^^^ maskOf 9 (codeV Z)) % 512
  rw [codeV_add, maskOf_add, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 9)
    (maskOf_lt 9 _) (maskOf_lt 9 _))]

theorem isHerm_conj (g : Matrix (Fin 3) (Fin 3) F4) {Y : Matrix (Fin 3) (Fin 3) F4}
    (hY : IsHerm Y) : IsHerm (g * Y * (bar g)ᵀ) := by
  have hY' : Yᵀ = bar Y := by
    ext i j
    exact hY i j
  have h : (g * Y * (bar g)ᵀ)ᵀ = bar (g * Y * (bar g)ᵀ) := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hY', bar_mul, bar_mul, ← bar_transpose,
      bar_bar, Matrix.mul_assoc]
  intro i j
  have := congrFun (congrFun h i) j
  rw [transpose_apply] at this
  exact this

theorem isHerm_bar {Y : Matrix (Fin 3) (Fin 3) F4} (hY : IsHerm Y) : IsHerm (bar Y) := by
  intro i j
  rw [bar_apply, bar_apply, hY i j]

@[expose] def act (g : Matrix (Fin 3) (Fin 3) F4) (m : Fin 512) : Fin 512 :=
  code (g * herm m * (bar g)ᵀ)

@[expose] def fld (m : Fin 512) : Fin 512 := code (bar (herm m))

theorem herm_act (g : Matrix (Fin 3) (Fin 3) F4) (m : Fin 512) :
    herm (act g m) = g * herm m * (bar g)ᵀ :=
  herm_code (isHerm_conj g (isHerm_herm m))

theorem herm_fld (m : Fin 512) : herm (fld m) = bar (herm m) :=
  herm_code (isHerm_bar (isHerm_herm m))

theorem act_mul (g h : Matrix (Fin 3) (Fin 3) F4) (m : Fin 512) :
    act (g * h) m = act g (act h m) := by
  rw [act, act, herm_act, bar_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

theorem act_one (m : Fin 512) : act 1 m = m := by
  rw [act, bar_one, transpose_one, Matrix.one_mul, Matrix.mul_one, code_herm]

theorem act_xor (g : Matrix (Fin 3) (Fin 3) F4) (m m' : Fin 512) :
    act g (m ^^^ m') = act g m ^^^ act g m' := by
  rw [act, herm_xor, Matrix.mul_add, Matrix.add_mul, code_add]
  rfl

theorem fld_fld (m : Fin 512) : fld (fld m) = m := by
  rw [fld, herm_fld, bar_bar, code_herm]

theorem fld_xor (m m' : Fin 512) : fld (m ^^^ m') = fld m ^^^ fld m' := by
  rw [fld, herm_xor, bar_add, code_add]
  rfl

theorem fld_act (g : Matrix (Fin 3) (Fin 3) F4) (m : Fin 512) :
    fld (act g m) = act (bar g) (fld m) := by
  rw [fld, herm_act, act, herm_fld, bar_mul, bar_mul, bar_transpose, bar_bar]

@[expose] def actN (g : Matrix (Fin 3) (Fin 3) F4) (m : ℕ) : ℕ :=
  (act g ⟨m % 512, Nat.mod_lt _ (by norm_num)⟩ : ℕ)

@[expose] def fldN (m : ℕ) : ℕ := (fld ⟨m % 512, Nat.mod_lt _ (by norm_num)⟩ : ℕ)

theorem fin_xor_mk (a b : ℕ) :
    ((⟨(a ^^^ b) % 512, Nat.mod_lt _ (by norm_num)⟩ : Fin 512)) =
      ⟨a % 512, Nat.mod_lt _ (by norm_num)⟩ ^^^ ⟨b % 512, Nat.mod_lt _ (by norm_num)⟩ := by
  apply Fin.ext
  show (a ^^^ b) % 2 ^ 9 = ((a % 2 ^ 9) ^^^ (b % 2 ^ 9)) % 2 ^ 9
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)))]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  cases decide (i < 9) <;> simp

theorem val_xor (x y : Fin 512) : ((x ^^^ y : Fin 512) : ℕ) = (x : ℕ) ^^^ (y : ℕ) :=
  Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 9) x.2 y.2)

theorem xorLin_actN (g : Matrix (Fin 3) (Fin 3) F4) : XorLin (actN g) := fun a b => by
  rw [actN, actN, actN, fin_xor_mk, act_xor, val_xor]

theorem xorLin_fldN : XorLin fldN := fun a b => by
  rw [fldN, fldN, fldN, fin_xor_mk, fld_xor, val_xor]

theorem actN_val (g : Matrix (Fin 3) (Fin 3) F4) (m : Fin 512) : actN g m = act g m := by
  rw [actN]
  congr 2
  exact Fin.ext (Nat.mod_eq_of_lt m.2)

theorem fldN_val (m : Fin 512) : fldN m = fld m := by
  rw [fldN]
  congr 2
  exact Fin.ext (Nat.mod_eq_of_lt m.2)

@[expose] def cols (g : Matrix (Fin 3) (Fin 3) F4) : List ℕ := matOf 9 (actN g)

theorem actM_cols (g : Matrix (Fin 3) (Fin 3) F4) (m : Fin 512) :
    actM (cols g) m = act g m := by
  rw [cols, actM_matOf (xorLin_actN g) 9 m m.2, actN_val]

abbrev W9 : Type := Wn 9

@[expose] def toW9 : Fin 512 ≃ W9 where
  toFun m := toW 9 m
  invFun w := ⟨maskOf 9 (Multiplicative.toAdd w), maskOf_lt 9 _⟩
  left_inv m := Fin.ext (maskOf_bvec m.2)
  right_inv w := by
    show Multiplicative.ofAdd (bvec 9 (maskOf 9 (Multiplicative.toAdd w))) = w
    rw [bvec_maskOf]
    rfl

theorem toW9_apply (m : Fin 512) : toW9 m = toW 9 m := rfl

theorem toW9_xor (m m' : Fin 512) : toW9 (m ^^^ m') = toW9 m * toW9 m' := by
  rw [toW9_apply, toW9_apply, toW9_apply, ← toW_xor]
  show Multiplicative.ofAdd (bvec 9 ((m ^^^ m' : Fin 512) : ℕ)) =
    Multiplicative.ofAdd (bvec 9 ((m : ℕ) ^^^ m'))
  rw [bvec_val, bvec_xor]

@[expose] def autOf (f f' : Fin 512 → Fin 512) (hf : ∀ m m', f (m ^^^ m') = f m ^^^ f m')
    (h1 : ∀ m, f' (f m) = m) (h2 : ∀ m, f (f' m) = m) : MulAut W9 where
  toFun w := toW9 (f (toW9.symm w))
  invFun w := toW9 (f' (toW9.symm w))
  left_inv w := by simp [h1]
  right_inv w := by simp [h2]
  map_mul' w w' := by
    have e : toW9.symm (w * w') = toW9.symm w ^^^ toW9.symm w' := by
      apply toW9.injective
      rw [toW9_xor, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [e, hf, toW9_xor]

theorem autOf_toW9 (f f' : Fin 512 → Fin 512) (hf : ∀ m m', f (m ^^^ m') = f m ^^^ f m')
    (h1 : ∀ m, f' (f m) = m) (h2 : ∀ m, f (f' m) = m) (m : Fin 512) :
    autOf f f' hf h1 h2 (toW9 m) = toW9 (f m) := by
  show toW9 (f (toW9.symm (toW9 m))) = toW9 (f m)
  rw [Equiv.symm_apply_apply]

@[expose] def rho9 : GL (Fin 3) F4 →* MulAut W9 where
  toFun g := autOf (act g) (act (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4)) (act_xor _)
    (fun m => by rw [← act_mul, Units.inv_mul, act_one])
    (fun m => by rw [← act_mul, Units.mul_inv, act_one])
  map_one' := by
    ext w
    obtain ⟨m, rfl⟩ := toW9.surjective w
    rw [autOf_toW9, Units.val_one, act_one]
    rfl
  map_mul' g h := by
    ext w
    obtain ⟨m, rfl⟩ := toW9.surjective w
    rw [MulAut.mul_apply, autOf_toW9, autOf_toW9, autOf_toW9, Units.val_mul, act_mul]

theorem rho9_toW9 (g : GL (Fin 3) F4) (m : Fin 512) :
    rho9 g (toW9 m) = toW9 (act g m) := by
  show toW9 (act g (toW9.symm (toW9 m))) = _
  rw [Equiv.symm_apply_apply]

@[expose] def fld9 : MulAut W9 := autOf fld fld fld_xor fld_fld fld_fld

theorem fld9_toW9 (m : Fin 512) : fld9 (toW9 m) = toW9 (fld m) := by
  show toW9 (fld (toW9.symm (toW9 m))) = _
  rw [Equiv.symm_apply_apply]

theorem fld9_mul_self : fld9 * fld9 = 1 := by
  ext w
  obtain ⟨m, rfl⟩ := toW9.surjective w
  rw [MulAut.mul_apply, fld9_toW9, fld9_toW9, fld_fld]
  rfl

@[expose] def frobGL : GL (Fin 3) F4 ≃* GL (Fin 3) F4 :=
  Units.mapEquiv (cjRing.mapMatrix (m := Fin 3)).toMulEquiv

theorem coe_frobGL (g : GL (Fin 3) F4) : ((frobGL g : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
    bar g := rfl

theorem frobGL_frobGL (g : GL (Fin 3) F4) : frobGL (frobGL g) = g := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL, bar_bar]

theorem fld9_mul_rho9 (g : GL (Fin 3) F4) : fld9 * rho9 g = rho9 (frobGL g) * fld9 := by
  ext w
  obtain ⟨m, rfl⟩ := toW9.surjective w
  rw [MulAut.mul_apply, MulAut.mul_apply, rho9_toW9, fld9_toW9, fld9_toW9, rho9_toW9, coe_frobGL,
    fld_act]

end CFSG.Quasithin.H13.Ch9.Herm9

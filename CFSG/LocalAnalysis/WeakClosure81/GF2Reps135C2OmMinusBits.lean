module

public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin

@[expose] def o8mBit : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ℕ
  | .inl i => 2 * i
  | .inr (.inl i) => 2 * i + 1
  | .inr (.inr t) => 6 + t

@[expose] def o8mVec {K : Type*} [Zero K] [One K] (x : ℕ) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K :=
  fun a => if x.testBit (o8mBit a) then 1 else 0

@[expose] def o8mPolarBit (x v : ℕ) : Bool :=
  (x.testBit 0 && v.testBit 1) ^^ (x.testBit 1 && v.testBit 0) ^^
    (x.testBit 2 && v.testBit 3) ^^ (x.testBit 3 && v.testBit 2) ^^
    (x.testBit 4 && v.testBit 5) ^^ (x.testBit 5 && v.testBit 4) ^^
    (x.testBit 6 && v.testBit 7) ^^ (x.testBit 7 && v.testBit 6)

@[expose] def o8mNormBit (v : ℕ) : Bool :=
  (v.testBit 0 && v.testBit 1) ^^ (v.testBit 2 && v.testBit 3) ^^
    (v.testBit 4 && v.testBit 5) ^^ v.testBit 6 ^^ (v.testBit 6 && v.testBit 7) ^^ v.testBit 7

@[expose] def o8mReflBit (v x : ℕ) : ℕ := if o8mPolarBit x v then x ^^^ v else x

@[expose] def o8mWordBit (w : List ℕ) (x : ℕ) : ℕ := w.foldr o8mReflBit x

@[expose] def o8mEvenWord (w : List ℕ) : Bool := w.length % 2 == 0 && w.all o8mNormBit

@[expose] def o8mWordCol (w : List ℕ) (j : ℕ) : ℕ := o8mWordBit w (2 ^ (2 * j))

@[expose] def o8mDeltaBit (col : ℕ → ℕ) (i : Fin 3) : Bool :=
  let e : ℕ → ℕ → Bool := fun r c => (col c).testBit (2 * r)
  if i.val = 0 then e 0 0
  else if i.val = 1 then (e 0 0 && e 1 1) ^^ (e 0 1 && e 1 0)
  else (e 0 0 && ((e 1 1 && e 2 2) ^^ (e 1 2 && e 2 1))) ^^
    (e 0 1 && ((e 1 0 && e 2 2) ^^ (e 1 2 && e 2 0))) ^^
    (e 0 2 && ((e 1 0 && e 2 1) ^^ (e 1 1 && e 2 0)))

@[expose] def o8mMinorProdBit (col : ℕ → ℕ) (m : ℕ) : Bool :=
  (!m.testBit 0 || o8mDeltaBit col 0) && (!m.testBit 1 || o8mDeltaBit col 1) &&
    (!m.testBit 2 || o8mDeltaBit col 2)

private theorem o8mBI_ite_mul {K : Type*} [MulZeroOneClass K] (p q : Bool) :
    (if p then (1 : K) else 0) * (if q then 1 else 0) = if p && q then 1 else 0 := by
  cases p <;> cases q <;> simp

private theorem o8mBI_ite_sq {K : Type*} [MulZeroOneClass K] (p : Bool) :
    (if p then (1 : K) else 0) * (if p then 1 else 0) = if p then 1 else 0 := by
  cases p <;> simp

private theorem o8mBI_ite_add {K : Type*} [Semiring K] [CharP K 2] (p q : Bool) :
    (if p then (1 : K) else 0) + (if q then 1 else 0) = if p ^^ q then 1 else 0 := by
  cases p <;> cases q <;> simp [CharTwo.add_self_eq_zero]

private theorem o8mBI_bit_e0 : o8mBit (Sum.inl 0) = 0 := rfl

private theorem o8mBI_bit_f0 : o8mBit (Sum.inr (Sum.inl 0)) = 1 := rfl

private theorem o8mBI_bit_e1 : o8mBit (Sum.inl 1) = 2 := rfl

private theorem o8mBI_bit_f1 : o8mBit (Sum.inr (Sum.inl 1)) = 3 := rfl

private theorem o8mBI_bit_e2 : o8mBit (Sum.inl 2) = 4 := rfl

private theorem o8mBI_bit_f2 : o8mBit (Sum.inr (Sum.inl 2)) = 5 := rfl

private theorem o8mBI_bit_a0 : o8mBit (Sum.inr (Sum.inr 0)) = 6 := rfl

private theorem o8mBI_bit_a1 : o8mBit (Sum.inr (Sum.inr 1)) = 7 := rfl

private theorem o8mBI_bit_injective : Function.Injective o8mBit := by
  decide +kernel

private theorem o8mBI_polar_prop (p0 q0 p1 q1 p2 q2 p3 q3 : Bool) :
    (((((p0 ^^ q0) ^^ (p1 ^^ q1)) ^^ (p2 ^^ q2)) ^^ (p3 ^^ q3)) = true) =
      ((q0 ^^ p0 ^^ q1 ^^ p1 ^^ q2 ^^ p2 ^^ q3 ^^ p3) = true) := by
  revert p0 q0 p1 q1 p2 q2 p3 q3
  decide +kernel

theorem o8mVec_two_pow {K : Type*} [Zero K] [One K] (a : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    (o8mVec (2 ^ o8mBit a) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) = Pi.single a 1 := by
  funext a'
  simp only [o8mVec, Pi.single_apply, Nat.testBit_two_pow]
  by_cases h : a' = a
  · subst h; simp
  · have hb : o8mBit a ≠ o8mBit a' := fun hh => h (o8mBI_bit_injective hh).symm
    simp [h, hb]

theorem o8mVec_xor {K : Type*} [Field K] [CharP K 2] (x v : ℕ) :
    (o8mVec (x ^^^ v) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) = o8mVec x + o8mVec v := by
  funext a
  simp only [o8mVec, Pi.add_apply, Nat.testBit_xor]
  rw [← o8mBI_ite_add]

theorem quadMinus_o8mVec {K : Type*} [Field K] [CharP K 2] (v : ℕ) :
    quadMinus 4 K 1 1 (o8mVec v) = if o8mNormBit v then 1 else 0 := by
  rw [quadMinus_apply, Fin.sum_univ_three]
  simp only [one_mul, pow_two, o8mVec]
  rw [o8mBI_bit_e0, o8mBI_bit_f0, o8mBI_bit_e1, o8mBI_bit_f1, o8mBI_bit_e2, o8mBI_bit_f2,
    o8mBI_bit_a0, o8mBI_bit_a1]
  simp only [o8mBI_ite_sq, o8mBI_ite_mul, o8mBI_ite_add]
  simp only [o8mNormBit]
  congr 1

theorem polar_quadMinus_o8mVec {K : Type*} [Field K] [CharP K 2] (v x : ℕ) :
    QuadraticMap.polar (quadMinus 4 K 1 1) (o8mVec v) (o8mVec x) =
      if o8mPolarBit x v then 1 else 0 := by
  rw [polar_quadMinus, Fin.sum_univ_three]
  simp only [one_mul, CharTwo.two_eq_zero, zero_mul, add_zero]
  simp only [o8mVec]
  rw [o8mBI_bit_e0, o8mBI_bit_f0, o8mBI_bit_e1, o8mBI_bit_f1, o8mBI_bit_e2, o8mBI_bit_f2,
    o8mBI_bit_a0, o8mBI_bit_a1]
  simp only [o8mBI_ite_mul, o8mBI_ite_add]
  simp only [o8mPolarBit]
  congr 1
  rw [show (v.testBit 0 && x.testBit 1) = (x.testBit 1 && v.testBit 0) from Bool.and_comm _ _,
    show (v.testBit 2 && x.testBit 3) = (x.testBit 3 && v.testBit 2) from Bool.and_comm _ _,
    show (v.testBit 4 && x.testBit 5) = (x.testBit 5 && v.testBit 4) from Bool.and_comm _ _,
    show (v.testBit 6 && x.testBit 7) = (x.testBit 7 && v.testBit 6) from Bool.and_comm _ _]
  exact o8mBI_polar_prop _ _ _ _ _ _ _ _

theorem reflect_o8mVec {K : Type*} [Field K] [CharP K 2] {v : ℕ} (hv : o8mNormBit v = true)
    (x : ℕ) :
    CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K 1 1) (o8mVec v) (o8mVec x) =
      o8mVec (o8mReflBit v x) := by
  have hQ : quadMinus 4 K 1 1 (o8mVec v) = 1 := by
    rw [quadMinus_o8mVec, hv]; rfl
  have hQne : quadMinus 4 K 1 1 (o8mVec v) ≠ 0 := by rw [hQ]; exact one_ne_zero
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply (Q := quadMinus 4 K 1 1) (v := o8mVec v)
    (x := o8mVec x) hQne, hQ, polar_quadMinus_o8mVec]
  rw [div_one]
  by_cases hp : o8mPolarBit x v = true
  · rw [if_pos hp, one_smul, CharTwo.sub_eq_add, ← o8mVec_xor, o8mReflBit, if_pos hp]
  · rw [if_neg hp, o8mReflBit, if_neg hp]
    rw [zero_smul, sub_zero]

theorem o8mWordBit_append (w w' : List ℕ) (x : ℕ) :
    o8mWordBit (w ++ w') x = o8mWordBit w (o8mWordBit w' x) := by
  simp only [o8mWordBit]
  rw [List.foldr_append]

@[expose] def o8mBoolMat {n : ℕ} (E : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun r c => if E r c then 1 else 0

theorem o8mBoolMat_det_ne_zero {n : ℕ} {k : Type*} [Field k] [CharP k 2]
    {E F : Fin n → Fin n → Bool} (h : o8mBoolMat E * o8mBoolMat F = 1) :
    (Matrix.of fun r c => if E r c then (1 : k) else 0).det ≠ 0 := by
  let ψ : ZMod 2 →+* k := ZMod.castHom (dvd_refl 2) k
  have hmap : (o8mBoolMat E).map ψ = Matrix.of (fun r c => if E r c then (1 : k) else 0) := by
    ext r c
    by_cases hb : E r c <;> simp [o8mBoolMat, Matrix.map_apply, hb]
  have hmul : (o8mBoolMat E).map ψ * (o8mBoolMat F).map ψ = 1 := by
    rw [← Matrix.map_mul, h]
    exact Matrix.map_one ψ (map_zero ψ) (map_one ψ)
  have hdet : ((o8mBoolMat E).map ψ).det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hmul
  rwa [hmap] at hdet

end CFSG.LocalAnalysis.WeakClosure81

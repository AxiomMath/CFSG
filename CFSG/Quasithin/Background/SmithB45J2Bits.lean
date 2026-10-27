module

public import CFSG.CharacterTheory.SteinbergBYFieldFour

public section

namespace CFSG.Quasithin.J2Bits

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open scoped Matrix

structure BV where
  re : ℕ
  im : ℕ
deriving DecidableEq

namespace BV

@[expose] def get (a : BV) (i : ℕ) : FieldFour := ⟨a.re.testBit i, a.im.testBit i⟩

@[expose] def toVec (a : BV) : Fin 6 → FieldFour := fun i => a.get i

@[expose] def zero : BV := ⟨0, 0⟩

@[expose] def add (a b : BV) : BV := ⟨a.re ^^^ b.re, a.im ^^^ b.im⟩

@[expose] def smul (c : FieldFour) (a : BV) : BV :=
  match c.re, c.im with
  | false, false => ⟨0, 0⟩
  | true, false => a
  | false, true => ⟨a.im, a.re ^^^ a.im⟩
  | true, true => ⟨a.re ^^^ a.im, a.re⟩

@[expose] def frob (a : BV) : BV := ⟨a.re ^^^ a.im, a.im⟩

@[expose] def eqv (a b : BV) : Bool := a.re % 64 == b.re % 64 && a.im % 64 == b.im % 64

@[expose] def nz (a : BV) (q : ℕ) : Bool := a.re.testBit q || a.im.testBit q

theorem get_zero (i : ℕ) : zero.get i = 0 := by
  simp only [get, zero, Nat.zero_testBit]
  rfl

theorem get_add (a b : BV) (i : ℕ) : (a.add b).get i = a.get i + b.get i := by
  simp only [get, add, Nat.testBit_xor]
  rfl

theorem get_smul (c : FieldFour) (a : BV) (i : ℕ) : (a.smul c).get i = c * a.get i := by
  obtain ⟨cr, ci⟩ := c
  have key : ∀ x y : Bool, ∀ cr ci : Bool,
      (⟨cr, ci⟩ : FieldFour) * ⟨x, y⟩ =
        ⟨xor (cr && x) (ci && y), xor (xor (cr && y) (ci && x)) (ci && y)⟩ := fun _ _ _ _ => rfl
  simp only [get]
  rw [key]
  cases cr <;> cases ci <;> simp only [smul, Nat.testBit_xor, Nat.zero_testBit] <;>
    cases a.re.testBit i <;> cases a.im.testBit i <;> rfl

theorem get_frob (a : BV) (i : ℕ) : a.frob.get i = FieldFour.frob (a.get i) := by
  simp only [get, frob, Nat.testBit_xor]
  rfl

theorem toVec_zero : zero.toVec = 0 := funext fun i => get_zero i

theorem toVec_add (a b : BV) : (a.add b).toVec = a.toVec + b.toVec :=
  funext fun i => get_add a b i

theorem toVec_smul (c : FieldFour) (a : BV) : (a.smul c).toVec = c • a.toVec :=
  funext fun i => get_smul c a i

theorem toVec_frob (a : BV) : a.frob.toVec = fun i => FieldFour.frob (a.toVec i) :=
  funext fun i => get_frob a i

theorem testBit_mod (x i : ℕ) : (x % 64).testBit i = (decide (i < 6) && x.testBit i) := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.testBit_mod_two_pow]

theorem eqv_iff (a b : BV) : a.eqv b = true ↔ a.toVec = b.toVec := by
  simp only [eqv, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    have e1 := congrArg (fun x => x.testBit i) h1
    have e2 := congrArg (fun x => x.testBit i) h2
    simp only [testBit_mod, i.isLt, decide_true, Bool.true_and] at e1 e2
    simp only [toVec, get, e1, e2]
  · intro h
    have hb : ∀ i : Fin 6, a.re.testBit i = b.re.testBit i ∧ a.im.testBit i = b.im.testBit i :=
      fun i => by
        have := congrFun h i
        simp only [toVec, get, FieldFour.mk.injEq] at this
        exact this
    refine ⟨Nat.eq_of_testBit_eq fun i => ?_, Nat.eq_of_testBit_eq fun i => ?_⟩ <;>
      rw [testBit_mod, testBit_mod] <;> by_cases hi : i < 6 <;> simp only [hi, decide_true,
        decide_false, Bool.true_and, Bool.false_and]
    · exact (hb ⟨i, hi⟩).1
    · exact (hb ⟨i, hi⟩).2

theorem nz_iff (a : BV) (q : ℕ) : a.nz q = true ↔ a.get q ≠ 0 := by
  simp only [nz, get, Bool.or_eq_true, ne_eq]
  constructor
  · rintro (h | h) e <;> simp only [FieldFour.ext_iff] at e
    · exact absurd e.1 (by rw [h]; decide)
    · exact absurd e.2 (by rw [h]; decide)
  · intro h
    by_contra hc
    simp only [not_or, Bool.not_eq_true] at hc
    exact h (by rw [hc.1, hc.2]; rfl)

end BV

structure BM where
  c0 : BV
  c1 : BV
  c2 : BV
  c3 : BV
  c4 : BV
  c5 : BV
deriving DecidableEq

namespace BM

@[expose] def col (m : BM) : Fin 6 → BV := ![m.c0, m.c1, m.c2, m.c3, m.c4, m.c5]

@[expose] def toMat (m : BM) : Matrix (Fin 6) (Fin 6) FieldFour :=
  Matrix.of fun i j => (m.col j).get i

@[expose] def mv (m : BM) (v : BV) : BV :=
  (((((m.c0.smul (v.get 0)).add (m.c1.smul (v.get 1))).add (m.c2.smul (v.get 2))).add
    (m.c3.smul (v.get 3))).add (m.c4.smul (v.get 4))).add (m.c5.smul (v.get 5))

@[expose] def mul (m n : BM) : BM :=
  ⟨m.mv n.c0, m.mv n.c1, m.mv n.c2, m.mv n.c3, m.mv n.c4, m.mv n.c5⟩

@[expose] def one : BM := ⟨⟨1, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨8, 0⟩, ⟨16, 0⟩, ⟨32, 0⟩⟩

@[expose] def frob (m : BM) : BM :=
  ⟨m.c0.frob, m.c1.frob, m.c2.frob, m.c3.frob, m.c4.frob, m.c5.frob⟩

@[expose] def eqv (m n : BM) : Bool :=
  m.c0.eqv n.c0 && m.c1.eqv n.c1 && m.c2.eqv n.c2 && m.c3.eqv n.c3 && m.c4.eqv n.c4 &&
    m.c5.eqv n.c5

@[expose] def key (m : BM) : ℕ :=
  m.c0.re % 64 + 64 * (m.c0.im % 64 + 64 * (m.c1.re % 64 + 64 * (m.c1.im % 64 +
    64 * (m.c2.re % 64 + 64 * (m.c2.im % 64 + 64 * (m.c3.re % 64 + 64 * (m.c3.im % 64 +
      64 * (m.c4.re % 64 + 64 * (m.c4.im % 64 + 64 * (m.c5.re % 64 + 64 * (m.c5.im % 64)))))))))))

theorem toMat_apply (m : BM) (i j : Fin 6) : m.toMat i j = (m.col j).toVec i := rfl

theorem toVec_mv (m : BM) (v : BV) : (m.mv v).toVec = m.toMat *ᵥ v.toVec := by
  funext i
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  show (m.mv v).get i = m.c0.get i * v.get 0 + m.c1.get i * v.get 1 + m.c2.get i * v.get 2 +
    m.c3.get i * v.get 3 + m.c4.get i * v.get 4 + m.c5.get i * v.get 5
  simp only [mv, BV.get_add, BV.get_smul]
  ring

theorem col_mul (m n : BM) (j : Fin 6) : (m.mul n).col j = m.mv (n.col j) := by
  fin_cases j <;> rfl

theorem toMat_mul (m n : BM) : (m.mul n).toMat = m.toMat * n.toMat := by
  refine Matrix.ext fun i j => ?_
  rw [toMat_apply, col_mul, toVec_mv]
  rfl

theorem toMat_one : one.toMat = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_frob (m : BM) : m.frob.toMat = m.toMat.map FieldFour.frob := by
  refine Matrix.ext fun i j => ?_
  fin_cases j <;> exact BV.get_frob _ _

theorem eqv_iff (m n : BM) : m.eqv n = true ↔ m.toMat = n.toMat := by
  have hcol : m.toMat = n.toMat ↔ ∀ j, (m.col j).toVec = (n.col j).toVec := by
    constructor
    · intro h j
      funext i
      exact congrFun (congrFun h i) j
    · intro h
      exact Matrix.ext fun i j => congrFun (h j) i
  rw [hcol, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ,
    Fin.forall_fin_succ, Fin.forall_fin_one]
  simp only [eqv, Bool.and_eq_true, ← BV.eqv_iff, and_assoc]
  rfl

end BM

end CFSG.Quasithin.J2Bits

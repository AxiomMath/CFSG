module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.ONanRec.F2

@[expose] def dmul : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 2, 3, 0, 5, 6, 7, 4],
    ![2, 3, 0, 1, 6, 7, 4, 5],
    ![3, 0, 1, 2, 7, 4, 5, 6],
    ![4, 7, 6, 5, 0, 3, 2, 1],
    ![5, 4, 7, 6, 1, 0, 3, 2],
    ![6, 5, 4, 7, 2, 1, 0, 3],
    ![7, 6, 5, 4, 3, 2, 1, 0]]

@[expose] def dinv : Fin 8 → Fin 8 := ![0, 3, 2, 1, 4, 5, 6, 7]

@[expose] def ck : Fin 8 → Fin 8 → ZMod 4 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 1, 1, 1],
    ![0, 3, 3, 3, 0, 3, 3, 3],
    ![0, 0, 3, 3, 0, 0, 3, 3],
    ![0, 0, 0, 3, 0, 0, 0, 3],
    ![0, 0, 0, 0, 0, 0, 0, 0]]

@[expose] def me : Fin 8 → Fin 3 → Fin 3 → ZMod 4 :=
  ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]],
    ![![1, 1, 0], ![3, 0, 1], ![1, 0, 0]],
    ![![0, 1, 1], ![0, 3, 0], ![1, 1, 0]],
    ![![0, 0, 1], ![1, 0, 3], ![0, 1, 1]],
    ![![0, 0, 3], ![0, 3, 0], ![3, 0, 0]],
    ![![0, 3, 3], ![3, 0, 1], ![0, 0, 3]],
    ![![3, 3, 0], ![0, 1, 0], ![0, 3, 3]],
    ![![3, 0, 0], ![1, 0, 3], ![3, 3, 0]]]

theorem dmul_assoc : ∀ a b c : Fin 8, dmul (dmul a b) c = dmul a (dmul b c) := by decide

theorem dmul_zero_left : ∀ b : Fin 8, dmul 0 b = b := by decide

theorem dmul_dinv : ∀ a : Fin 8, dmul (dinv a) a = 0 := by decide

theorem me_dmul : ∀ (a b : Fin 8) (i k : Fin 3),
    me (dmul a b) i k = me a i 0 * me b 0 k + me a i 1 * me b 1 k + me a i 2 * me b 2 k := by
  decide

theorem me_zero : ∀ i k : Fin 3, me 0 i k = if i = k then 1 else 0 := by decide

theorem ck_zero_left : ∀ b : Fin 8, ck 0 b = 0 := by decide

theorem ck_cocycle0 : ∀ a b c : Fin 8,
    ck a b + ck (dmul a b) c = (me a 0 0 + me a 0 2) * ck b c + ck a (dmul b c) := by decide

theorem ck_cocycle1 : ∀ a b c : Fin 8, (me a 1 0 + me a 1 2) * ck b c = 0 := by decide

theorem ck_cocycle2 : ∀ a b c : Fin 8,
    ck a b + ck (dmul a b) c = (me a 2 0 + me a 2 2) * ck b c + ck a (dmul b c) := by decide

theorem ck_inv :
    ∀ a : Fin 8, ck (dinv a) a = (me (dinv a) 0 0 + me (dinv a) 0 2) * ck a (dinv a) := by
  decide

theorem ck_inv1 : ∀ a : Fin 8, (me (dinv a) 1 0 + me (dinv a) 1 2) * ck a (dinv a) = 0 := by decide

theorem ck_inv2 :
    ∀ a : Fin 8, ck (dinv a) a = (me (dinv a) 2 0 + me (dinv a) 2 2) * ck a (dinv a) := by
  decide

@[ext] structure AlpE where
  d : Fin 8
  v0 : ZMod 4
  v1 : ZMod 4
  v2 : ZMod 4

namespace AlpE

instance instDecidableEq : DecidableEq AlpE := fun a b =>
  decidable_of_iff (a.d = b.d ∧ a.v0 = b.v0 ∧ a.v1 = b.v1 ∧ a.v2 = b.v2) (by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact AlpE.ext h1 h2 h3 h4
    · rintro rfl
      exact ⟨rfl, rfl, rfl, rfl⟩)

@[expose] def act (d : Fin 8) (i : Fin 3) (b : AlpE) : ZMod 4 :=
  me d i 0 * b.v0 + me d i 1 * b.v1 + me d i 2 * b.v2

@[expose] def mul (a b : AlpE) : AlpE :=
  ⟨dmul a.d b.d, a.v0 + act a.d 0 b + ck a.d b.d, a.v1 + act a.d 1 b,
    a.v2 + act a.d 2 b + ck a.d b.d⟩

@[expose] def inv (a : AlpE) : AlpE :=
  ⟨dinv a.d, -act (dinv a.d) 0 ⟨0, a.v0 + ck a.d (dinv a.d), a.v1, a.v2 + ck a.d (dinv a.d)⟩,
    -act (dinv a.d) 1 ⟨0, a.v0 + ck a.d (dinv a.d), a.v1, a.v2 + ck a.d (dinv a.d)⟩,
    -act (dinv a.d) 2 ⟨0, a.v0 + ck a.d (dinv a.d), a.v1, a.v2 + ck a.d (dinv a.d)⟩⟩

instance : One AlpE := ⟨⟨0, 0, 0, 0⟩⟩
instance : Mul AlpE := ⟨mul⟩
instance : Inv AlpE := ⟨inv⟩

theorem one_def : (1 : AlpE) = ⟨0, 0, 0, 0⟩ := rfl
theorem mul_def (a b : AlpE) : a * b = mul a b := rfl
theorem inv_def (a : AlpE) : a⁻¹ = inv a := rfl

theorem act_mul (a b c : AlpE) (i : Fin 3) :
    act (dmul a.d b.d) i c = act a.d i ⟨0, act b.d 0 c, act b.d 1 c, act b.d 2 c⟩ := by
  simp only [act, me_dmul]
  ring

theorem mul_assoc' (a b c : AlpE) : a * b * c = a * (b * c) := by
  show mul (mul a b) c = mul a (mul b c)
  have h0 := ck_cocycle0 a.d b.d c.d
  have h1 := ck_cocycle1 a.d b.d c.d
  have h2 := ck_cocycle2 a.d b.d c.d
  simp only [mul, act_mul]
  congr 1
  · exact dmul_assoc a.d b.d c.d
  · simp only [act]
    linear_combination h0
  · simp only [act]
    linear_combination -h1
  · simp only [act]
    linear_combination h2

theorem one_mul' (a : AlpE) : 1 * a = a := by
  show mul ⟨0, 0, 0, 0⟩ a = a
  simp only [mul, act, me_zero, dmul_zero_left, ck_zero_left]
  congr 1 <;> simp

theorem inv_mul_cancel' (a : AlpE) : a⁻¹ * a = 1 := by
  show mul (inv a) a = ⟨0, 0, 0, 0⟩
  have h0 := ck_inv a.d
  have h1 := ck_inv1 a.d
  have h2 := ck_inv2 a.d
  simp only [mul, inv, dmul_dinv, act]
  congr 1
  · linear_combination h0
  · linear_combination -h1
  · linear_combination h2

instance instGroup : Group AlpE := Group.ofLeftAxioms mul_assoc' one_mul' inv_mul_cancel'

@[expose] def equivProd : AlpE ≃ Fin 8 × ZMod 4 × ZMod 4 × ZMod 4 where
  toFun s := (s.d, s.v0, s.v1, s.v2)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype AlpE := Fintype.ofEquiv _ equivProd.symm

@[expose] def gen : Fin 5 → AlpE :=
  ![AlpE.mk 0 1 0 0, AlpE.mk 0 0 1 0, AlpE.mk 0 0 0 1, AlpE.mk 1 0 0 0, AlpE.mk 4 0 0 0]

@[expose] def zc : AlpE := gen 0 ^ 2 * gen 2 ^ 2

end AlpE

end CFSG.OddStandard.ONanRec.F2

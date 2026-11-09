module

public import CFSG.Quasithin.Recognition.G112A2D6ZornBasic
import CFSG.LinearAlgebra.F2NatMat

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Open

@[expose] def z6cU (u x : z6O) : z6O := quasithinZornMul (quasithinZornMul u x) (z6Bar u)

@[expose] def z6MV (M : Fin 3 → Fin 3 → ZMod 2) (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  fun i => M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2

@[expose] def z6S (M N : Fin 3 → Fin 3 → ZMod 2) (x : z6O) : z6O :=
  (x.2.2.2, z6MV N x.2.2.1, z6MV M x.2.1, x.1)

@[expose] def z6Ms : List ((Fin 3 → Fin 3 → ZMod 2) × (Fin 3 → Fin 3 → ZMod 2)) :=
  [(![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]]),
    (![![0, 0, 1], ![0, 1, 1], ![1, 1, 0]], ![![1, 1, 1], ![1, 1, 0], ![1, 0, 0]]),
    (![![0, 1, 0], ![1, 1, 0], ![0, 0, 1]], ![![1, 1, 0], ![1, 0, 0], ![0, 0, 1]]),
    (![![0, 1, 0], ![1, 1, 1], ![0, 1, 1]], ![![0, 1, 1], ![1, 0, 0], ![1, 0, 1]]),
    (![![0, 1, 1], ![1, 0, 0], ![1, 0, 1]], ![![0, 1, 0], ![1, 1, 1], ![0, 1, 1]]),
    (![![0, 1, 1], ![1, 0, 1], ![1, 1, 1]], ![![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]),
    (![![1, 0, 0], ![0, 0, 1], ![0, 1, 0]], ![![1, 0, 0], ![0, 0, 1], ![0, 1, 0]]),
    (![![1, 0, 1], ![0, 0, 1], ![1, 1, 0]], ![![1, 1, 0], ![1, 1, 1], ![0, 1, 0]]),
    (![![1, 1, 0], ![1, 0, 0], ![0, 0, 1]], ![![0, 1, 0], ![1, 1, 0], ![0, 0, 1]]),
    (![![1, 1, 1], ![1, 0, 0], ![1, 0, 1]], ![![0, 1, 0], ![1, 0, 1], ![0, 1, 1]])]

theorem z6_mv_add (M : Fin 3 → Fin 3 → ZMod 2) (v w : Fin 3 → ZMod 2) :
    z6MV M (v + w) = z6MV M v + z6MV M w := by
  funext i
  simp only [z6MV, Pi.add_apply]
  ring

theorem z6_mv_smul (M : Fin 3 → Fin 3 → ZMod 2) (c : ZMod 2) (v : Fin 3 → ZMod 2) :
    z6MV M (c • v) = c • z6MV M v := by
  funext i
  simp only [z6MV, Pi.smul_apply, smul_eq_mul]
  ring

@[expose] def z6cUL (u : z6O) : z6O →ₗ[ZMod 2] z6O where
  toFun := z6cU u
  map_add' x y := by
    simp only [z6cU, z6_mul_add_right, z6_mul_add_left]
  map_smul' c x := by
    rcases z6_zmod2 c with rfl | rfl
    · simp [z6cU, z6_mul_zero_left, z6_mul_zero_right]
    · simp [z6cU]

@[expose] def z6SL (M N : Fin 3 → Fin 3 → ZMod 2) : z6O →ₗ[ZMod 2] z6O where
  toFun := z6S M N
  map_add' x y := by
    obtain ⟨a, u, v, b⟩ := x
    obtain ⟨a', u', v', b'⟩ := y
    simp only [z6S, Prod.mk_add_mk, z6_mv_add]
  map_smul' c x := by
    obtain ⟨a, u, v, b⟩ := x
    simp only [z6S, Prod.smul_mk, RingHom.id_apply, z6_mv_smul]

theorem z6_coords (P : z6O → Prop)
    (h : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2, P (a, ![p0, p1, p2], ![q0, q1, q2], b)) : ∀ u : z6O, P u := by
  rintro ⟨a, p, q, b⟩
  have hp : p = ![p 0, p 1, p 2] := by
    funext i
    fin_cases i <;> rfl
  have hq : q = ![q 0, q 1, q 2] := by
    funext i
    fin_cases i <;> rfl
  have := h a b (p 0) (p 1) (p 2) (q 0) (q 1) (q 2)
  rw [← hp, ← hq] at this
  exact this

private abbrev BZ : Type := Bool × (Bool × Bool × Bool) × (Bool × Bool × Bool) × Bool

private def v3 (t : Bool × Bool × Bool) : Fin 3 → ZMod 2 :=
  ![CFSG.F2NatMat.ent t.1, CFSG.F2NatMat.ent t.2.1, CFSG.F2NatMat.ent t.2.2]

private def toZ (x : BZ) : z6O := (CFSG.F2NatMat.ent x.1, v3 x.2.1, v3 x.2.2.1, CFSG.F2NatMat.ent x.2.2.2)

open CFSG.F2NatMat in
private def zmulP (x y : BZ) : BZ :=
  (bx (bx (bx (x.1 && y.1) (x.2.1.1 && y.2.2.1.1)) (x.2.1.2.1 && y.2.2.1.2.1))
      (x.2.1.2.2 && y.2.2.1.2.2),
    (bx (bx (x.1 && y.2.1.1) (y.2.2.2 && x.2.1.1))
        (bx (x.2.2.1.2.1 && y.2.2.1.2.2) (x.2.2.1.2.2 && y.2.2.1.2.1)),
      bx (bx (x.1 && y.2.1.2.1) (y.2.2.2 && x.2.1.2.1))
        (bx (x.2.2.1.2.2 && y.2.2.1.1) (x.2.2.1.1 && y.2.2.1.2.2)),
      bx (bx (x.1 && y.2.1.2.2) (y.2.2.2 && x.2.1.2.2))
        (bx (x.2.2.1.1 && y.2.2.1.2.1) (x.2.2.1.2.1 && y.2.2.1.1))),
    (bx (bx (y.1 && x.2.2.1.1) (x.2.2.2 && y.2.2.1.1))
        (bx (x.2.1.2.1 && y.2.1.2.2) (x.2.1.2.2 && y.2.1.2.1)),
      bx (bx (y.1 && x.2.2.1.2.1) (x.2.2.2 && y.2.2.1.2.1))
        (bx (x.2.1.2.2 && y.2.1.1) (x.2.1.1 && y.2.1.2.2)),
      bx (bx (y.1 && x.2.2.1.2.2) (x.2.2.2 && y.2.2.1.2.2))
        (bx (x.2.1.1 && y.2.1.2.1) (x.2.1.2.1 && y.2.1.1))),
    bx (bx (bx (x.2.2.2 && y.2.2.2) (x.2.2.1.1 && y.2.1.1)) (x.2.2.1.2.1 && y.2.1.2.1))
      (x.2.2.1.2.2 && y.2.1.2.2))

private def barB (x : BZ) : BZ := (x.2.2.2, x.2.1, x.2.2.1, x.1)

open CFSG.F2NatMat in
private def trB (x : BZ) : Bool := bx x.1 x.2.2.2

open CFSG.F2NatMat in
private def nrmB (x : BZ) : Bool :=
  bx (bx (bx (x.1 && x.2.2.2) (x.2.1.1 && x.2.2.1.1)) (x.2.1.2.1 && x.2.2.1.2.1))
    (x.2.1.2.2 && x.2.2.1.2.2)

open CFSG.F2NatMat in
private def xorB (x y : BZ) : BZ :=
  (bx x.1 y.1, (bx x.2.1.1 y.2.1.1, bx x.2.1.2.1 y.2.1.2.1, bx x.2.1.2.2 y.2.1.2.2),
    (bx x.2.2.1.1 y.2.2.1.1, bx x.2.2.1.2.1 y.2.2.1.2.1, bx x.2.2.1.2.2 y.2.2.1.2.2),
    bx x.2.2.2 y.2.2.2)

private def zeroB : BZ := (false, (false, false, false), (false, false, false), false)

open CFSG.F2NatMat in
private theorem toZ_mul (x y : BZ) : quasithinZornMul (toZ x) (toZ y) = toZ (zmulP x y) := by
  obtain ⟨a, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, b⟩ := x
  obtain ⟨c, ⟨s0, s1, s2⟩, ⟨t0, t1, t2⟩, d⟩ := y
  simp only [quasithinZornMul, toZ, zmulP, v3, quasithinCross, Fin.sum_univ_three, bx_eq,
    ent_xor, ent_and]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp; ring
  · funext i; fin_cases i <;> simp [sub_eq_add_neg] <;> ring
  · funext i; fin_cases i <;> simp [sub_eq_add_neg]
  · simp; ring

open CFSG.F2NatMat in
private theorem toZ_bar (x : BZ) : z6Bar (toZ x) = toZ (barB x) := by
  obtain ⟨a, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, b⟩ := x
  simp only [z6Bar, toZ, barB]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;>
    · funext i; exact zmod2_neg _

open CFSG.F2NatMat in
private theorem toZ_tr (x : BZ) : z6Tr (toZ x) = ent (trB x) := by
  obtain ⟨a, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, b⟩ := x
  simp only [z6Tr, toZ, trB, bx_eq, ent_xor]

open CFSG.F2NatMat in
private theorem toZ_nrm (x : BZ) : z6Nrm (toZ x) = ent (nrmB x) := by
  obtain ⟨a, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, b⟩ := x
  simp only [z6Nrm, toZ, nrmB, v3, Fin.sum_univ_three, bx_eq, ent_xor, ent_and]
  simp; ring

open CFSG.F2NatMat in
private theorem toZ_xor (x y : BZ) : toZ (xorB x y) = toZ x + toZ y := by
  obtain ⟨a, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, b⟩ := x
  obtain ⟨c, ⟨s0, s1, s2⟩, ⟨t0, t1, t2⟩, d⟩ := y
  simp only [toZ, xorB, v3, bx_eq, ent_xor]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;>
    · funext i; fin_cases i <;> simp

private theorem toZ_zero : toZ zeroB = 0 := by
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;>
    · funext i; fin_cases i <;> rfl

open CFSG.F2NatMat in
private theorem toZ_inj {x y : BZ} (h : toZ x = toZ y) : x = y := by
  obtain ⟨a, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, b⟩ := x
  obtain ⟨c, ⟨s0, s1, s2⟩, ⟨t0, t1, t2⟩, d⟩ := y
  simp only [toZ, v3, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e := fun i => congrFun h2 i
  have f := fun i => congrFun h3 i
  have e0 := e 0; have e1 := e 1; have e2 := e 2
  have f0 := f 0; have f1 := f 1; have f2 := f 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at e0 e1 e2 f0 f1 f2
  rw [ent_inj] at h1 h4 e0 e1 e2 f0 f1 f2
  subst h1 h4 e0 e1 e2 f0 f1 f2
  rfl

private def EB : Fin 8 → BZ :=
  ![(true, (false, false, false), (false, false, false), false),
    (false, (false, false, false), (false, false, false), true),
    (false, (true, false, false), (false, false, false), false),
    (false, (false, true, false), (false, false, false), false),
    (false, (false, false, true), (false, false, false), false),
    (false, (false, false, false), (true, false, false), false),
    (false, (false, false, false), (false, true, false), false),
    (false, (false, false, false), (false, false, true), false)]

private theorem toZ_E (i : Fin 8) : z6E i = toZ (EB i) := by
  fin_cases i <;> (refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))) <;> funext j <;>
    fin_cases j <;> rfl

open CFSG.F2NatMat in
private theorem toZ_of (a b p0 p1 p2 q0 q1 q2 : ZMod 2) :
    ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) =
      toZ (decide (a = 1), (decide (p0 = 1), decide (p1 = 1), decide (p2 = 1)),
        (decide (q0 = 1), decide (q1 = 1), decide (q2 = 1)), decide (b = 1)) := by
  simp only [toZ, v3, ent_decide_eq_one]

private def cUB (u x : BZ) : BZ := zmulP (zmulP u x) (barB u)

private theorem toZ_cU (u x : BZ) : z6cU (toZ u) (toZ x) = toZ (cUB u x) := by
  rw [z6cU, toZ_mul, toZ_bar, toZ_mul, cUB]

private def colsB (u : BZ) (k : Fin 8) : BZ := cUB u (EB k)

private def prodTab : Fin 8 → Fin 8 → Option (Fin 8) :=
  ![![some 0, none, some 2, some 3, some 4, none, none, none],
    ![none, some 1, none, none, none, some 5, some 6, some 7],
    ![none, some 2, none, some 7, some 6, some 0, none, none],
    ![none, some 3, some 7, none, some 5, none, some 0, none],
    ![none, some 4, some 6, some 5, none, none, none, some 0],
    ![some 5, none, some 1, none, none, none, some 4, some 3],
    ![some 6, none, none, some 1, none, some 4, none, some 2],
    ![some 7, none, none, none, some 1, some 3, some 2, none]]

private theorem prodTab_spec : ∀ i j : Fin 8, zmulP (EB i) (EB j) = (prodTab i j).elim zeroB EB := by
  decide +kernel

private theorem zmulP_zero (x : BZ) : zmulP x zeroB = zeroB := by
  obtain ⟨a, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, b⟩ := x
  simp [zmulP, zeroB, CFSG.F2NatMat.bx]

private theorem zero_zmulP (x : BZ) : zmulP zeroB x = zeroB := by
  obtain ⟨a, ⟨p0, p1, p2⟩, ⟨q0, q1, q2⟩, b⟩ := x
  simp [zmulP, zeroB, CFSG.F2NatMat.bx]

private theorem cU_basis (u : BZ) (i j : Fin 8) :
    cUB u (zmulP (EB i) (EB j)) = (prodTab i j).elim zeroB (colsB u) := by
  rw [prodTab_spec]
  cases prodTab i j with
  | none => simp only [Option.elim, cUB, zmulP_zero, zero_zmulP]
  | some k => rfl

open CFSG.F2NatMat in
private def stepB (bit : Bool) (acc col : BZ) : BZ := cond bit (xorB acc col) acc

private def linG (cols : Fin 8 → BZ) (x : BZ) : BZ :=
  stepB x.2.2.2 (stepB x.2.2.1.2.2 (stepB x.2.2.1.2.1 (stepB x.2.2.1.1 (stepB x.2.1.2.2
    (stepB x.2.1.2.1 (stepB x.2.1.1 (stepB x.1 zeroB (cols 0)) (cols 2)) (cols 3)) (cols 4))
    (cols 5)) (cols 6)) (cols 7)) (cols 1)

private theorem linG_EB : ∀ x : BZ, linG EB x = x := by decide +kernel

private theorem lin_step (f : z6O →ₗ[ZMod 2] z6O) {bit : Bool} {acc acc' col col' : BZ}
    (hacc : f (toZ acc) = toZ acc') (hcol : f (toZ col) = toZ col') :
    f (toZ (stepB bit acc col)) = toZ (stepB bit acc' col') := by
  cases bit
  · exact hacc
  · simp only [stepB, Bool.cond_true, toZ_xor, map_add, hacc, hcol]

private theorem lin_toZ (f : z6O →ₗ[ZMod 2] z6O) (cols : Fin 8 → BZ)
    (hc : ∀ k, f (toZ (EB k)) = toZ (cols k)) (x : BZ) : f (toZ x) = toZ (linG cols x) := by
  have h0 : f (toZ zeroB) = toZ zeroB := by rw [toZ_zero, map_zero]
  conv_lhs => rw [← linG_EB x]
  exact lin_step f (lin_step f (lin_step f (lin_step f (lin_step f (lin_step f (lin_step f
    (lin_step f h0 (hc 0)) (hc 2)) (hc 3)) (hc 4)) (hc 5)) (hc 6)) (hc 7)) (hc 1)

private theorem zmod2_eq_zero_of_decide {x : ZMod 2} (h : decide (x = 1) = false) : x = 0 := by
  revert x; decide

private abbrev SZ : Type := ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × ℕ

private def laneZ (X : SZ) (k : ℕ) : BZ :=
  (X.1.testBit k, (X.2.1.1.testBit k, X.2.1.2.1.testBit k, X.2.1.2.2.testBit k),
    (X.2.2.1.1.testBit k, X.2.2.1.2.1.testBit k, X.2.2.1.2.2.testBit k), X.2.2.2.testBit k)

private def zmulS (x y : SZ) : SZ :=
  ((((x.1 &&& y.1) ^^^ (x.2.1.1 &&& y.2.2.1.1)) ^^^ (x.2.1.2.1 &&& y.2.2.1.2.1)) ^^^
      (x.2.1.2.2 &&& y.2.2.1.2.2),
    ((((x.1 &&& y.2.1.1) ^^^ (y.2.2.2 &&& x.2.1.1)) ^^^
        ((x.2.2.1.2.1 &&& y.2.2.1.2.2) ^^^ (x.2.2.1.2.2 &&& y.2.2.1.2.1))),
      (((x.1 &&& y.2.1.2.1) ^^^ (y.2.2.2 &&& x.2.1.2.1)) ^^^
        ((x.2.2.1.2.2 &&& y.2.2.1.1) ^^^ (x.2.2.1.1 &&& y.2.2.1.2.2))),
      (((x.1 &&& y.2.1.2.2) ^^^ (y.2.2.2 &&& x.2.1.2.2)) ^^^
        ((x.2.2.1.1 &&& y.2.2.1.2.1) ^^^ (x.2.2.1.2.1 &&& y.2.2.1.1)))),
    ((((y.1 &&& x.2.2.1.1) ^^^ (x.2.2.2 &&& y.2.2.1.1)) ^^^
        ((x.2.1.2.1 &&& y.2.1.2.2) ^^^ (x.2.1.2.2 &&& y.2.1.2.1))),
      (((y.1 &&& x.2.2.1.2.1) ^^^ (x.2.2.2 &&& y.2.2.1.2.1)) ^^^
        ((x.2.1.2.2 &&& y.2.1.1) ^^^ (x.2.1.1 &&& y.2.1.2.2))),
      (((y.1 &&& x.2.2.1.2.2) ^^^ (x.2.2.2 &&& y.2.2.1.2.2)) ^^^
        ((x.2.1.1 &&& y.2.1.2.1) ^^^ (x.2.1.2.1 &&& y.2.1.1)))),
    (((x.2.2.2 &&& y.2.2.2) ^^^ (x.2.2.1.1 &&& y.2.1.1)) ^^^ (x.2.2.1.2.1 &&& y.2.1.2.1)) ^^^
      (x.2.2.1.2.2 &&& y.2.1.2.2))

private theorem lane_zmulS (x y : SZ) (k : ℕ) :
    laneZ (zmulS x y) k = zmulP (laneZ x k) (laneZ y k) := by
  simp only [laneZ, zmulS, zmulP, Nat.testBit_and, Nat.testBit_xor, CFSG.F2NatMat.bx_eq]

private def barS (x : SZ) : SZ := (x.2.2.2, x.2.1, x.2.2.1, x.1)

private theorem lane_barS (x : SZ) (k : ℕ) : laneZ (barS x) k = barB (laneZ x k) := rfl

private def xorS (x y : SZ) : SZ :=
  (x.1 ^^^ y.1, (x.2.1.1 ^^^ y.2.1.1, x.2.1.2.1 ^^^ y.2.1.2.1, x.2.1.2.2 ^^^ y.2.1.2.2),
    (x.2.2.1.1 ^^^ y.2.2.1.1, x.2.2.1.2.1 ^^^ y.2.2.1.2.1, x.2.2.1.2.2 ^^^ y.2.2.1.2.2),
    x.2.2.2 ^^^ y.2.2.2)

private theorem lane_xorS (x y : SZ) (k : ℕ) : laneZ (xorS x y) k = xorB (laneZ x k) (laneZ y k) := by
  simp only [laneZ, xorS, xorB, Nat.testBit_xor, CFSG.F2NatMat.bx_eq]

private def zeroS : SZ := (0, (0, 0, 0), (0, 0, 0), 0)

private theorem lane_zeroS (k : ℕ) : laneZ zeroS k = zeroB := by
  simp [laneZ, zeroS, zeroB]

private def onesS : ℕ := 2 ^ 256 - 1

private theorem testBit_onesS {k : ℕ} (hk : k < 256) : onesS.testBit k = true := by
  rw [onesS, Nat.testBit_two_pow_sub_one]; simpa using hk

private def cbit (b : Bool) : ℕ := cond b onesS 0

private theorem testBit_cbit (b : Bool) {k : ℕ} (hk : k < 256) : (cbit b).testBit k = b := by
  cases b
  · simp [cbit]
  · exact testBit_onesS hk

private def constS (x : BZ) : SZ :=
  (cbit x.1, (cbit x.2.1.1, cbit x.2.1.2.1, cbit x.2.1.2.2),
    (cbit x.2.2.1.1, cbit x.2.2.1.2.1, cbit x.2.2.1.2.2), cbit x.2.2.2)

private theorem lane_constS (x : BZ) {k : ℕ} (hk : k < 256) : laneZ (constS x) k = x := by
  simp only [laneZ, constS, testBit_cbit _ hk]

private def idxM (j : ℕ) : ℕ := CFSG.F2NatMat.build (fun k => CFSG.F2NatMat.bitK k j) 256

private def laneU : SZ := (idxM 0, (idxM 1, idxM 2, idxM 3), (idxM 4, idxM 5, idxM 6), idxM 7)

private def ofCodeB (k : ℕ) : BZ :=
  (k.testBit 0, (k.testBit 1, k.testBit 2, k.testBit 3), (k.testBit 4, k.testBit 5, k.testBit 6),
    k.testBit 7)

private theorem lane_U {k : ℕ} (hk : k < 256) : laneZ laneU k = ofCodeB k := by
  simp only [laneZ, laneU, idxM, CFSG.F2NatMat.testBit_build, CFSG.F2NatMat.bitK_eq,
    decide_eq_true hk, Bool.true_and, ofCodeB]

private def codeB (u : BZ) : ℕ :=
  cond u.1 1 0 + cond u.2.1.1 2 0 + cond u.2.1.2.1 4 0 + cond u.2.1.2.2 8 0 +
    cond u.2.2.1.1 16 0 + cond u.2.2.1.2.1 32 0 + cond u.2.2.1.2.2 64 0 + cond u.2.2.2 128 0

private theorem codeB_spec : ∀ u : BZ, codeB u < 256 ∧ ofCodeB (codeB u) = u := by
  decide +kernel

private def trS (x : SZ) : ℕ := x.1 ^^^ x.2.2.2

private theorem testBit_trS (x : SZ) (k : ℕ) : (trS x).testBit k = trB (laneZ x k) := by
  simp only [trS, trB, laneZ, Nat.testBit_xor, CFSG.F2NatMat.bx_eq]

private def nrmS (x : SZ) : ℕ :=
  (((x.1 &&& x.2.2.2) ^^^ (x.2.1.1 &&& x.2.2.1.1)) ^^^ (x.2.1.2.1 &&& x.2.2.1.2.1)) ^^^
    (x.2.1.2.2 &&& x.2.2.1.2.2)

private theorem testBit_nrmS (x : SZ) (k : ℕ) : (nrmS x).testBit k = nrmB (laneZ x k) := by
  simp only [nrmS, nrmB, laneZ, Nat.testBit_and, Nat.testBit_xor, CFSG.F2NatMat.bx_eq]

private def diffS (x y : SZ) : ℕ :=
  (x.1 ^^^ y.1) ||| (x.2.1.1 ^^^ y.2.1.1) ||| (x.2.1.2.1 ^^^ y.2.1.2.1) |||
    (x.2.1.2.2 ^^^ y.2.1.2.2) ||| (x.2.2.1.1 ^^^ y.2.2.1.1) ||| (x.2.2.1.2.1 ^^^ y.2.2.1.2.1) |||
    (x.2.2.1.2.2 ^^^ y.2.2.1.2.2) ||| (x.2.2.2 ^^^ y.2.2.2)

private theorem xor_eq_false {a b : Bool} (h : (a ^^ b) = false) : a = b := by
  revert a b; decide

private theorem lane_eq_of_diffS {x y : SZ} {k : ℕ} (h : (diffS x y).testBit k = false) :
    laneZ x k = laneZ y k := by
  simp only [diffS, Nat.testBit_or, Nat.testBit_xor, Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  simp only [laneZ, xor_eq_false h1, xor_eq_false h2, xor_eq_false h3, xor_eq_false h4,
    xor_eq_false h5, xor_eq_false h6, xor_eq_false h7, xor_eq_false h8]

private theorem diffS_of_lane_eq {x y : SZ} {k : ℕ} (h : laneZ x k = laneZ y k) :
    (diffS x y).testBit k = false := by
  simp only [laneZ, Prod.mk.injEq] at h
  obtain ⟨h1, ⟨h2, h3, h4⟩, ⟨h5, h6, h7⟩, h8⟩ := h
  simp only [diffS, Nat.testBit_or, Nat.testBit_xor, h1, h2, h3, h4, h5, h6, h7, h8,
    Bool.xor_self, Bool.or_self]

private def validV : ℕ := trS laneU &&& nrmS laneU

private def cUS (u x : SZ) : SZ := zmulS (zmulS u x) (barS u)

private def colS (k : Fin 8) : SZ := cUS laneU (constS (EB k))

private theorem lane_colS {u : BZ} {k : ℕ} (hk : k < 256) (hu : ofCodeB k = u) (i : Fin 8) :
    laneZ (colS i) k = colsB u i := by
  rw [colS, cUS, lane_zmulS, lane_zmulS, lane_barS, lane_U hk, lane_constS _ hk, hu]
  rfl

private theorem checkF1S : ∀ i j : Fin 8,
    validV &&& diffS ((prodTab i j).elim zeroS colS) (zmulS (colS i) (colS j)) = 0 := by
  decide +kernel

private def stepS (bit : Bool) (acc col : SZ) : SZ := cond bit (xorS acc col) acc

private def linGS (cols : Fin 8 → SZ) (x : BZ) : SZ :=
  stepS x.2.2.2 (stepS x.2.2.1.2.2 (stepS x.2.2.1.2.1 (stepS x.2.2.1.1 (stepS x.2.1.2.2
    (stepS x.2.1.2.1 (stepS x.2.1.1 (stepS x.1 zeroS (cols 0)) (cols 2)) (cols 3)) (cols 4))
    (cols 5)) (cols 6)) (cols 7)) (cols 1)

private theorem lane_stepS (bit : Bool) (acc col : SZ) (k : ℕ) :
    laneZ (stepS bit acc col) k = stepB bit (laneZ acc k) (laneZ col k) := by
  cases bit
  · rfl
  · exact lane_xorS acc col k

private theorem lane_linGS (cols : Fin 8 → SZ) (x : BZ) (k : ℕ) :
    laneZ (linGS cols x) k = linG (fun i => laneZ (cols i) k) x := by
  simp only [linGS, linG, lane_stepS, lane_zeroS]

set_option synthInstance.maxSize 4096 in
private theorem checkF4S : ∀ x : BZ, trB x = false →
    (x.2.1 = (false, false, false) ∧ x.2.2.1 = (false, false, false) ∧ x.1 = x.2.2.2) ∨
      validV &&& (onesS ^^^ diffS (linGS colS x) (constS x)) = 0 := by
  decide +kernel

private theorem V_testBit {u : BZ} (htr : trB u = true) (hnr : nrmB u = true) :
    validV.testBit (codeB u) = true := by
  obtain ⟨hk, hu⟩ := codeB_spec u
  rw [validV, Nat.testBit_and, testBit_trS, testBit_nrmS, lane_U hk, hu, htr, hnr]
  rfl

private theorem checkF1 : ∀ u : BZ, trB u = true → nrmB u = true → ∀ i j : Fin 8,
    (prodTab i j).elim zeroB (colsB u) = zmulP (colsB u i) (colsB u j) := by
  intro u htr hnr i j
  obtain ⟨hk, hu⟩ := codeB_spec u
  have hV := V_testBit htr hnr
  have h := congrArg (fun n => Nat.testBit n (codeB u)) (checkF1S i j)
  simp only [Nat.testBit_and, hV, Bool.true_and, Nat.zero_testBit] at h
  have e := lane_eq_of_diffS h
  rw [lane_zmulS, lane_colS hk hu, lane_colS hk hu] at e
  rw [← e]
  cases prodTab i j with
  | none => exact (lane_zeroS _).symm
  | some m => exact (lane_colS hk hu m).symm

set_option synthInstance.maxSize 4096 in
private theorem checkF4 : ∀ u : BZ, trB u = true → nrmB u = true → ∀ x : BZ, trB x = false →
    linG (colsB u) x = x → x.2.1 = (false, false, false) ∧ x.2.2.1 = (false, false, false) ∧
      x.1 = x.2.2.2 := by
  intro u htr hnr x hx hfix
  obtain ⟨hk, hu⟩ := codeB_spec u
  rcases checkF4S x hx with h | h
  · exact h
  · exfalso
    have hV := V_testBit htr hnr
    have h' := congrArg (fun n => Nat.testBit n (codeB u)) h
    simp only [Nat.testBit_and, hV, Bool.true_and, Nat.zero_testBit, Nat.testBit_xor,
      testBit_onesS hk] at h'
    have hd : (diffS (linGS colS x) (constS x)).testBit (codeB u) = false := by
      apply diffS_of_lane_eq
      rw [lane_linGS, lane_constS _ hk,
        show (fun i => laneZ (colS i) (codeB u)) = colsB u from funext (lane_colS hk hu), hfix]
    rw [hd] at h'
    exact absurd h' (by decide)

set_option synthInstance.maxSize 4096 in
theorem z6_F1_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 → ∀ i j : Fin 8,
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (quasithinZornMul (z6E i) (z6E j)) =
      quasithinZornMul (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (z6E i))
        (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (z6E j)) := by
  intro a b p0 p1 p2 q0 q1 q2
  rw [toZ_of]
  generalize (decide (a = 1), (decide (p0 = 1), decide (p1 = 1), decide (p2 = 1)),
    (decide (q0 = 1), decide (q1 = 1), decide (q2 = 1)), decide (b = 1)) = u
  rw [toZ_tr, toZ_nrm, CFSG.F2NatMat.ent_eq_one, CFSG.F2NatMat.ent_eq_one]
  intro htr hnr i j
  simp only [toZ_E, toZ_mul, toZ_cU]
  rw [cU_basis, checkF1 u htr hnr i j]
  rfl


theorem z6_F1 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → ∀ i j : Fin 8,
    z6cU u (quasithinZornMul (z6E i) (z6E j)) =
      quasithinZornMul (z6cU u (z6E i)) (z6cU u (z6E j)) :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∀ i j : Fin 8,
    z6cU u (quasithinZornMul (z6E i) (z6E j)) =
      quasithinZornMul (z6cU u (z6E i)) (z6cU u (z6E j))) z6_F1_c

set_option synthInstance.maxSize 4096 in
theorem z6_F2_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 → ∀ i : Fin 8,
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O)
      (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O)
        (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (z6E i))) = z6E i := by
  decide +kernel

theorem z6_F2 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → ∀ i : Fin 8,
    z6cU u (z6cU u (z6cU u (z6E i))) = z6E i :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∀ i : Fin 8,
    z6cU u (z6cU u (z6cU u (z6E i))) = z6E i) z6_F2_c

set_option synthInstance.maxSize 4096 in
theorem z6_F2one_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) z6One = z6One := by
  decide +kernel

theorem z6_F2one : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → z6cU u z6One = z6One :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → z6cU u z6One = z6One) z6_F2one_c

set_option synthInstance.maxSize 4096 in
theorem z6_F3_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 → ∀ i : Fin 8,
    z6cU (z6Bar ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O)) (z6E i) =
      z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O)
        (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (z6E i)) := by
  decide +kernel

theorem z6_F3 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → ∀ i : Fin 8,
    z6cU (z6Bar u) (z6E i) = z6cU u (z6cU u (z6E i)) :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∀ i : Fin 8,
    z6cU (z6Bar u) (z6E i) = z6cU u (z6cU u (z6E i))) z6_F3_c

set_option synthInstance.maxSize 4096 in
theorem z6_F4_c : ∀ a b p0 p1 p2 q0 q1 q2 c d s0 s1 s2 t0 t1 t2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Tr ((c, ![s0, s1, s2], ![t0, t1, t2], d) : z6O) = 0 →
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) ((c, ![s0, s1, s2], ![t0, t1, t2], d) : z6O) =
        ((c, ![s0, s1, s2], ![t0, t1, t2], d) : z6O) →
    s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ t0 = 0 ∧ t1 = 0 ∧ t2 = 0 ∧ c = d := by
  intro a b p0 p1 p2 q0 q1 q2 c d s0 s1 s2 t0 t1 t2 h1 h2 h3 h4
  rw [toZ_of a] at h1 h2 h4
  rw [toZ_of c] at h3 h4
  rw [toZ_tr, CFSG.F2NatMat.ent_eq_one] at h1
  rw [toZ_nrm, CFSG.F2NatMat.ent_eq_one] at h2
  rw [toZ_tr, CFSG.F2NatMat.ent_eq_zero] at h3
  generalize (decide (a = 1), (decide (p0 = 1), decide (p1 = 1), decide (p2 = 1)),
    (decide (q0 = 1), decide (q1 = 1), decide (q2 = 1)), decide (b = 1)) = U at h1 h2 h4
  have hl := lin_toZ (z6cUL (toZ U)) (colsB U) (fun k => toZ_cU U (EB k))
  obtain ⟨e1, e2, e3⟩ := checkF4 U h1 h2 _ h3 (toZ_inj ((hl _).symm.trans h4))
  simp only [Prod.mk.injEq] at e1 e2 e3
  obtain ⟨e10, e11, e12⟩ := e1
  obtain ⟨e20, e21, e22⟩ := e2
  refine ⟨zmod2_eq_zero_of_decide e10, zmod2_eq_zero_of_decide e11, zmod2_eq_zero_of_decide e12,
    zmod2_eq_zero_of_decide e20, zmod2_eq_zero_of_decide e21, zmod2_eq_zero_of_decide e22, ?_⟩
  rw [← CFSG.F2NatMat.ent_decide_eq_one c, ← CFSG.F2NatMat.ent_decide_eq_one d, e3]

theorem z6_F4 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → ∀ x : z6O, z6Tr x = 0 →
    z6cU u x = x → x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ x.1 = x.2.2.2 := by
  refine z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∀ x : z6O, z6Tr x = 0 →
    z6cU u x = x → x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ x.1 = x.2.2.2) ?_
  intro a b p0 p1 p2 q0 q1 q2 h1 h2
  refine z6_coords (fun x => z6Tr x = 0 →
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) x = x →
      x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ x.1 = x.2.2.2) ?_
  intro c d s0 s1 s2 t0 t1 t2 hx hfix
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ :=
    z6_F4_c a b p0 p1 p2 q0 q1 q2 c d s0 s1 s2 t0 t1 t2 h1 h2 hx hfix
  refine ⟨?_, ?_, e6⟩
  · funext i
    fin_cases i <;> simp [e0, e1, e2]
  · funext i
    fin_cases i <;> simp [e3, e4, e5]

set_option synthInstance.maxSize 4096 in
theorem z6_F5_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    ∃ p ∈ z6Ms, z6S p.1 p.2 ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) =
      z6Bar ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) := by
  decide +kernel

theorem z6_F5 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 →
    ∃ p ∈ z6Ms, z6S p.1 p.2 u = z6Bar u :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∃ p ∈ z6Ms, z6S p.1 p.2 u = z6Bar u) z6_F5_c

theorem z6_S1 : ∀ p ∈ z6Ms, ∀ i j : Fin 8,
    z6S p.1 p.2 (quasithinZornMul (z6E i) (z6E j)) =
      quasithinZornMul (z6S p.1 p.2 (z6E i)) (z6S p.1 p.2 (z6E j)) := by
  decide +kernel

theorem z6_S2 : ∀ p ∈ z6Ms, ∀ i : Fin 8, z6S p.1 p.2 (z6S p.1 p.2 (z6E i)) = z6E i := by
  decide +kernel

end CFSG.Quasithin.G112A2


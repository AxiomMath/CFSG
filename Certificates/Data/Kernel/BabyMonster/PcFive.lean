module

public import Init

public section

namespace CFSG.KC.BM.PcFive

structure QV where
  a0 : Nat
  a1 : Nat
  a2 : Nat
  a3 : Nat
  c : Nat

structure CM where
  m01 : Nat
  m02 : Nat
  m03 : Nat
  m12 : Nat
  m13 : Nat
  m23 : Nat

@[expose] def QV.one : QV := ⟨0, 0, 0, 0, 0⟩

@[expose] def mulQ (m : CM) (a b : QV) : QV :=
  ⟨(a.a0 + b.a0) % 5, (a.a1 + b.a1) % 5, (a.a2 + b.a2) % 5, (a.a3 + b.a3) % 5,
    (a.c + b.c + a.a3 * (b.a0 * m.m03 + b.a1 * m.m13 + b.a2 * m.m23) +
      a.a2 * (b.a0 * m.m02 + b.a1 * m.m12) + a.a1 * (b.a0 * m.m01)) % 5⟩

@[expose] def powQ (m : CM) (r : QV) : Nat → QV
  | 0 => QV.one
  | k + 1 => mulQ m (powQ m r k) r

structure QAct where
  r0 : QV
  r1 : QV
  r2 : QV
  r3 : QV
  rz : QV

@[expose] def applyQ (m : CM) (A : QAct) (a : QV) : QV :=
  mulQ m (mulQ m (mulQ m (mulQ m (powQ m A.r0 a.a0) (powQ m A.r1 a.a1)) (powQ m A.r2 a.a2))
    (powQ m A.r3 a.a3)) (powQ m A.rz a.c)

structure G10 where
  g00 : Nat
  g01 : Nat
  g02 : Nat
  g03 : Nat
  g11 : Nat
  g12 : Nat
  g13 : Nat
  g22 : Nat
  g23 : Nat
  g33 : Nat

structure QF where
  r0 : QV
  r1 : QV
  r2 : QV
  r3 : QV
  g : G10

@[expose] def evalQF (F : QF) (a : QV) : QV :=
  ⟨(a.a0 * F.r0.a0 + a.a1 * F.r1.a0 + a.a2 * F.r2.a0 + a.a3 * F.r3.a0) % 5,
    (a.a0 * F.r0.a1 + a.a1 * F.r1.a1 + a.a2 * F.r2.a1 + a.a3 * F.r3.a1) % 5,
    (a.a0 * F.r0.a2 + a.a1 * F.r1.a2 + a.a2 * F.r2.a2 + a.a3 * F.r3.a2) % 5,
    (a.a0 * F.r0.a3 + a.a1 * F.r1.a3 + a.a2 * F.r2.a3 + a.a3 * F.r3.a3) % 5,
    (a.c + a.a0 * F.r0.c + a.a1 * F.r1.c + a.a2 * F.r2.c + a.a3 * F.r3.c +
      a.a0 * (a.a0 * F.g.g00 + a.a1 * F.g.g01 + a.a2 * F.g.g02 + a.a3 * F.g.g03) +
      a.a1 * (a.a1 * F.g.g11 + a.a2 * F.g.g12 + a.a3 * F.g.g13) +
      a.a2 * (a.a2 * F.g.g22 + a.a3 * F.g.g23) + a.a3 * (a.a3 * F.g.g33)) % 5⟩

@[expose] def cmFive : CM := ⟨4, 1, 4, 0, 3, 4⟩

@[expose] def xAct : QAct :=
  ⟨⟨0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 1, 0⟩, ⟨2, 2, 4, 2, 0⟩, ⟨1, 4, 4, 0, 1⟩, ⟨0, 0, 0, 0, 1⟩⟩

@[expose] def hAct : QAct :=
  ⟨⟨0, 1, 0, 0, 0⟩, ⟨3, 1, 1, 0, 1⟩, ⟨2, 2, 2, 0, 2⟩, ⟨1, 1, 1, 4, 2⟩, ⟨0, 0, 0, 0, 2⟩⟩

@[expose] def phi1 : QF :=
  ⟨⟨0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 1, 0⟩, ⟨2, 2, 4, 2, 3⟩, ⟨1, 4, 4, 0, 1⟩,
    ⟨0, 0, 2, 1, 0, 0, 2, 2, 1, 0⟩⟩

@[expose] def phi2 : QF :=
  ⟨⟨2, 2, 4, 2, 3⟩, ⟨1, 4, 4, 0, 1⟩, ⟨0, 1, 1, 0, 2⟩, ⟨3, 3, 2, 2, 3⟩,
    ⟨2, 1, 4, 4, 0, 0, 0, 0, 0, 0⟩⟩

@[expose] def phi3 : QF :=
  ⟨⟨0, 1, 1, 0, 2⟩, ⟨3, 3, 2, 2, 3⟩, ⟨2, 2, 4, 3, 0⟩, ⟨1, 2, 4, 2, 1⟩,
    ⟨0, 0, 0, 0, 0, 3, 1, 2, 0, 2⟩⟩

@[expose] def phi4 : QF :=
  ⟨⟨2, 2, 4, 3, 0⟩, ⟨1, 2, 4, 2, 1⟩, ⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0⟩,
    ⟨2, 0, 4, 4, 2, 0, 1, 0, 0, 0⟩⟩

@[expose] def phiAt (k : Nat) (a : QV) : QV :=
  bif k.beq 0 then a else bif k.beq 1 then evalQF phi1 a else bif k.beq 2 then evalQF phi2 a
  else bif k.beq 3 then evalQF phi3 a else evalQF phi4 a

@[expose] def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => f k && allBelow f k

@[expose] def nth : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, k + 1 => nth l k

@[expose] def QV.red (a : QV) : Prop := a.a0 < 5 ∧ a.a1 < 5 ∧ a.a2 < 5 ∧ a.a3 < 5 ∧ a.c < 5

@[expose] def decQ (n : Nat) : QV := ⟨n / 625 % 5, n / 125 % 5, n / 25 % 5, n / 5 % 5, n % 5⟩

@[expose] def QV.beq (a b : QV) : Bool :=
  a.a0.beq b.a0 && a.a1.beq b.a1 && a.a2.beq b.a2 && a.a3.beq b.a3 && a.c.beq b.c

@[expose] def phiOK (_ : Unit := ()) : Bool :=
  allBelow (fun n =>
    (evalQF phi1 (decQ n)).beq (applyQ cmFive xAct (decQ n)) &&
    (evalQF phi2 (decQ n)).beq (evalQF phi1 (evalQF phi1 (decQ n))) &&
    (evalQF phi3 (decQ n)).beq (evalQF phi2 (evalQF phi1 (decQ n))) &&
    (evalQF phi4 (decQ n)).beq (evalQF phi3 (evalQF phi1 (decQ n)))) 3125

structure V6 where
  e : Nat
  q : QV

@[expose] def V6.one : V6 := ⟨0, QV.one⟩

@[expose] def V6.beq (v w : V6) : Bool := v.e.beq w.e && v.q.beq w.q

@[expose] def V6.isOne (v : V6) : Bool := v.beq V6.one

@[expose] def dec (i : Nat) : V6 := ⟨i / 3125 % 5, decQ (i % 3125)⟩

@[expose] def mulV (v w : V6) : V6 := ⟨(v.e + w.e) % 5, mulQ cmFive (phiAt w.e v.q) w.q⟩

@[expose] def powV (v : V6) : Nat → V6
  | 0 => V6.one
  | k + 1 => mulV (powV v k) v

@[expose] def ord5 (v : V6) : Bool := (powV v 5).isOne

@[expose] def autAt (j : Nat) : List Nat :=
  bif j.beq 0 then [13493, 2585, 2177, 664, 17, 1]
  else bif j.beq 1 then [9294, 830, 1117, 971, 2794, 3] else [14446, 1921, 1226, 1322, 5, 4]

@[expose] def singleSrc : List Nat := [5, 45, 135, 145, 155, 160, 170, 175, 635, 740, 745]

@[expose] def singleTgt : List Nat := [96, 2859, 665, 682, 273, 342, 359, 1250, 440, 838, 783]

@[expose] def targets : List Nat := [1, 660, 30, 3125, 3126, 3127]

@[expose] def alphaV (ws : List Nat) (v : V6) : V6 :=
  mulV (mulV (mulV (mulV (mulV (powV (dec (nth ws 0)) v.e) (powV (dec (nth ws 1)) v.q.a0))
    (powV (dec (nth ws 2)) v.q.a1)) (powV (dec (nth ws 3)) v.q.a2))
    (powV (dec (nth ws 4)) v.q.a3)) (powV (dec (nth ws 5)) v.q.c)

@[expose] def V6.red (v : V6) : Prop := v.e < 5 ∧ v.q.red

inductive Fused : V6 → Prop
  | target {i : Nat} : i ∈ targets → Fused (dec i)
  | conj {v w g : V6} : g.red → w.red → mulV g v = mulV w g → Fused w → Fused v
  | aut {v : V6} {j : Nat} : j < 3 → Fused (alphaV (autAt j) v) → Fused v
  | pow {v : V6} {k : Nat} : ord5 v = true → 2 ≤ k → k < 5 → Fused (powV v k) → Fused v
  | single {m : Nat} : m < 11 → Fused (dec (nth singleTgt m)) → Fused (dec (nth singleSrc m))

@[expose] def CensusFact : Prop :=
  ∀ i < 15625, i ≠ 0 → ord5 (dec i) = true → Fused (dec i)

@[expose] def memN (n : Nat) : List Nat → Bool
  | [] => false
  | a :: l => n.beq a || memN n l

@[expose] def elemOK (rep : Nat → Nat) (nc i d : Nat) : Bool :=
  i.beq 0 || !(ord5 (dec i)) ||
    (Nat.blt (d / 15625) nc &&
      (mulV (dec (d % 15625)) (dec i)).beq (mulV (dec (rep (d / 15625))) (dec (d % 15625))))

@[expose] def chunkOK (rep : Nat → Nat) (nc : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | i, d :: ds => elemOK rep nc i d && chunkOK rep nc (i + 1) ds

@[expose] def stepOK (rep : Nat → Nat) (nc : Nat) (depth : List Nat) (c c' w : Nat) (v' : V6) :
    Bool :=
  Nat.blt c' nc && Nat.blt (nth depth c') (nth depth c) &&
    (mulV (dec w) v').beq (mulV (dec (rep c')) (dec w))

@[expose] def classOK (rep : Nat → Nat) (nc : Nat) (depth kind arg cls wit : List Nat) (c : Nat) :
    Bool :=
  let r := rep c
  let k := nth kind c
  let a := nth arg c
  bif k.beq 0 then memN r targets
  else bif k.beq 1 then Nat.blt a 3 &&
    stepOK rep nc depth c (nth cls c) (nth wit c) (alphaV (autAt a) (dec r))
  else bif k.beq 2 then Nat.ble 2 a && Nat.blt a 5 && ord5 (dec r) &&
    stepOK rep nc depth c (nth cls c) (nth wit c) (powV (dec r) a)
  else Nat.blt a 11 && r.beq (nth singleSrc a) &&
    stepOK rep nc depth c (nth cls c) (nth wit c) (dec (nth singleTgt a))

@[expose] def fusOK (rep : Nat → Nat) (nc : Nat) (depth kind arg cls wit : List Nat) : Bool :=
  allBelow (classOK rep nc depth kind arg cls wit) nc

end CFSG.KC.BM.PcFive

end

module

public import Certificates.Data.Kernel.BabyMonster.PcFive

public section

namespace CFSG.KC.MonPcSeven

open CFSG.KC.BM.PcFive (QV CM QAct G10 QF V6 nth allBelow memN)

@[expose] def mulQ (m : CM) (a b : QV) : QV :=
  ⟨(a.a0 + b.a0) % 7, (a.a1 + b.a1) % 7, (a.a2 + b.a2) % 7, (a.a3 + b.a3) % 7,
    (a.c + b.c + a.a3 * (b.a0 * m.m03 + b.a1 * m.m13 + b.a2 * m.m23) +
      a.a2 * (b.a0 * m.m02 + b.a1 * m.m12) + a.a1 * (b.a0 * m.m01)) % 7⟩

@[expose] def powQ (m : CM) (r : QV) : Nat → QV
  | 0 => ⟨0, 0, 0, 0, 0⟩
  | k + 1 => mulQ m (powQ m r k) r

@[expose] def applyQ (m : CM) (A : QAct) (a : QV) : QV :=
  mulQ m (mulQ m (mulQ m (mulQ m (powQ m A.r0 a.a0) (powQ m A.r1 a.a1)) (powQ m A.r2 a.a2))
    (powQ m A.r3 a.a3)) (powQ m A.rz a.c)

@[expose] def polyC (F : QF) (a : QV) : Nat :=
  a.a0 * F.r0.c + a.a1 * F.r1.c + a.a2 * F.r2.c + a.a3 * F.r3.c +
    a.a0 * (a.a0 * F.g.g00 + a.a1 * F.g.g01 + a.a2 * F.g.g02 + a.a3 * F.g.g03) +
    a.a1 * (a.a1 * F.g.g11 + a.a2 * F.g.g12 + a.a3 * F.g.g13) +
    a.a2 * (a.a2 * F.g.g22 + a.a3 * F.g.g23) + a.a3 * (a.a3 * F.g.g33)

@[expose] def evalQF (F : QF) (a : QV) : QV :=
  ⟨(a.a0 * F.r0.a0 + a.a1 * F.r1.a0 + a.a2 * F.r2.a0 + a.a3 * F.r3.a0) % 7,
    (a.a0 * F.r0.a1 + a.a1 * F.r1.a1 + a.a2 * F.r2.a1 + a.a3 * F.r3.a1) % 7,
    (a.a0 * F.r0.a2 + a.a1 * F.r1.a2 + a.a2 * F.r2.a2 + a.a3 * F.r3.a2) % 7,
    (a.a0 * F.r0.a3 + a.a1 * F.r1.a3 + a.a2 * F.r2.a3 + a.a3 * F.r3.a3) % 7,
    (a.c + polyC F a) % 7⟩

@[expose] def cmSeven : CM := ⟨1, 6, 6, 1, 0, 0⟩

@[expose] def uAct : QAct :=
  ⟨⟨1, 1, 0, 0, 3⟩, ⟨0, 1, 1, 0, 4⟩, ⟨0, 0, 1, 1, 5⟩, ⟨0, 0, 0, 1, 2⟩, ⟨0, 0, 0, 0, 1⟩⟩

@[expose] def phi1 : QF :=
  ⟨⟨1, 6, 1, 6, 5⟩, ⟨0, 1, 6, 1, 3⟩, ⟨0, 0, 1, 6, 4⟩, ⟨0, 0, 0, 1, 5⟩,
    ⟨6, 1, 0, 0, 3, 0, 0, 0, 0, 0⟩⟩

@[expose] def phi2 : QF :=
  ⟨⟨1, 5, 3, 3, 6⟩, ⟨0, 1, 5, 3, 0⟩, ⟨0, 0, 1, 5, 3⟩, ⟨0, 0, 0, 1, 3⟩,
    ⟨0, 3, 0, 0, 6, 0, 0, 0, 0, 0⟩⟩

@[expose] def phi3 : QF :=
  ⟨⟨1, 4, 6, 4, 4⟩, ⟨0, 1, 4, 6, 3⟩, ⟨0, 0, 1, 4, 4⟩, ⟨0, 0, 0, 1, 1⟩,
    ⟨2, 6, 0, 0, 2, 0, 0, 0, 0, 0⟩⟩

@[expose] def phi4 : QF :=
  ⟨⟨1, 3, 3, 1, 2⟩, ⟨0, 1, 3, 3, 3⟩, ⟨0, 0, 1, 3, 0⟩, ⟨0, 0, 0, 1, 6⟩,
    ⟨4, 3, 0, 0, 5, 0, 0, 0, 0, 0⟩⟩

@[expose] def phi5 : QF :=
  ⟨⟨1, 2, 1, 0, 5⟩, ⟨0, 1, 2, 1, 5⟩, ⟨0, 0, 1, 2, 5⟩, ⟨0, 0, 0, 1, 4⟩,
    ⟨5, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩⟩

@[expose] def phi6 : QF :=
  ⟨⟨1, 1, 0, 0, 6⟩, ⟨0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 5⟩, ⟨0, 0, 0, 1, 2⟩,
    ⟨4, 0, 0, 0, 4, 0, 0, 0, 0, 0⟩⟩

@[expose] def phiAt (k : Nat) (a : QV) : QV :=
  bif k.beq 0 then a else bif k.beq 1 then evalQF phi1 a else bif k.beq 2 then evalQF phi2 a
  else bif k.beq 3 then evalQF phi3 a else bif k.beq 4 then evalQF phi4 a
  else bif k.beq 5 then evalQF phi5 a else evalQF phi6 a

@[expose] def decA (n : Nat) : QV := ⟨n / 343 % 7, n / 49 % 7, n / 7 % 7, n % 7, 0⟩

@[expose] def phiRow (a : QV) : Bool :=
  let b := evalQF phi1 a
  (applyQ cmSeven uAct b).beq a && (evalQF phi2 a).beq (evalQF phi1 b) &&
    (evalQF phi3 a).beq (evalQF phi2 b) && (evalQF phi4 a).beq (evalQF phi3 b) &&
    (evalQF phi5 a).beq (evalQF phi4 b) && (evalQF phi6 a).beq (evalQF phi5 b)

@[expose] def phiOK (lo k : Nat) : Bool := allBelow (fun n => phiRow (decA (lo + n))) k

@[expose] def decQ (n : Nat) : QV := ⟨n / 2401 % 7, n / 343 % 7, n / 49 % 7, n / 7 % 7, n % 7⟩

@[expose] def dec (i : Nat) : V6 := ⟨i / 16807 % 7, decQ (i % 16807)⟩

@[expose] def mulV (v w : V6) : V6 := ⟨(v.e + w.e) % 7, mulQ cmSeven (phiAt w.e v.q) w.q⟩

@[expose] def powV (v : V6) : Nat → V6
  | 0 => ⟨0, ⟨0, 0, 0, 0, 0⟩⟩
  | k + 1 => mulV (powV v k) v

@[expose] def ord7 (v : V6) : Bool := (powV v 7).isOne

@[expose] def autAt (j : Nat) : List Nat :=
  bif j.beq 0 then [89895, 14406, 915, 185, 8, 6] else [86483, 6173, 1056, 65, 39, 3]

@[expose] def targets : List Nat :=
  [1, 42, 294, 2079, 2072, 2093, 12005, 12019, 12047, 12033, 12306, 12313, 12341, 12327, 12208,
    12222, 12243, 12229, 108045, 105644, 105647, 105646]

@[expose] def alphaV (ws : List Nat) (v : V6) : V6 :=
  mulV (mulV (mulV (mulV (mulV (powV (dec (nth ws 0)) v.e) (powV (dec (nth ws 1)) v.q.a0))
    (powV (dec (nth ws 2)) v.q.a1)) (powV (dec (nth ws 3)) v.q.a2))
    (powV (dec (nth ws 4)) v.q.a3)) (powV (dec (nth ws 5)) v.q.c)

@[expose] def redQ (a : QV) : Prop := a.a0 < 7 ∧ a.a1 < 7 ∧ a.a2 < 7 ∧ a.a3 < 7 ∧ a.c < 7

@[expose] def redV (v : V6) : Prop := v.e < 7 ∧ redQ v.q

inductive Fused : V6 → Prop
  | target {i : Nat} : i ∈ targets → Fused (dec i)
  | conj {v w g : V6} : redV g → redV w → mulV g v = mulV w g → Fused w → Fused v
  | aut {v : V6} {j : Nat} : j < 2 → Fused (alphaV (autAt j) v) → Fused v
  | pow {v : V6} {k : Nat} : ord7 v = true → 2 ≤ k → k < 7 → Fused (powV v k) → Fused v

@[expose] def CensusFact : Prop :=
  ∀ i < 117649, i ≠ 0 → Fused (dec i)

@[expose] def elemOK (rep : Nat → Nat) (nc i d : Nat) : Bool :=
  i.beq 0 ||
    (Nat.blt (d / 117649) nc &&
      (mulV (dec (d % 117649)) (dec i)).beq (mulV (dec (rep (d / 117649))) (dec (d % 117649))))

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
  else bif k.beq 1 then Nat.blt a 2 &&
    stepOK rep nc depth c (nth cls c) (nth wit c) (alphaV (autAt a) (dec r))
  else Nat.ble 2 a && Nat.blt a 7 && ord7 (dec r) &&
    stepOK rep nc depth c (nth cls c) (nth wit c) (powV (dec r) a)

@[expose] def fusOK (rep : Nat → Nat) (nc : Nat) (depth kind arg cls wit : List Nat) : Bool :=
  allBelow (classOK rep nc depth kind arg cls wit) nc

end CFSG.KC.MonPcSeven

end

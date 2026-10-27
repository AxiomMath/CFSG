module

public section

namespace CFSG.KC.A8Hold

@[expose] def pk (v0 v1 v2 v3 v4 v5 v6 v7 : Nat) : Nat :=
  v0 + 8 * (v1 + 8 * (v2 + 8 * (v3 + 8 * (v4 + 8 * (v5 + 8 * (v6 + 8 * v7))))))

@[expose] def gN (t x : Nat) : Nat := t / 8 ^ x % 8

@[expose] def compN (s t : Nat) : Nat :=
  pk (gN s (gN t 0)) (gN s (gN t 1)) (gN s (gN t 2)) (gN s (gN t 3)) (gN s (gN t 4))
    (gN s (gN t 5)) (gN s (gN t 6)) (gN s (gN t 7))

@[expose] def findN (t y : Nat) : Nat :=
  if gN t 0 = y then 0 else if gN t 1 = y then 1 else if gN t 2 = y then 2 else
  if gN t 3 = y then 3 else if gN t 4 = y then 4 else if gN t 5 = y then 5 else
  if gN t 6 = y then 6 else 7

@[expose] def invN (t : Nat) : Nat :=
  pk (findN t 0) (findN t 1) (findN t 2) (findN t 3) (findN t 4) (findN t 5) (findN t 6)
    (findN t 7)

@[expose] noncomputable def powN (k t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) t (fun _ ih => compN ih ih) k

@[expose] def idN : Nat := pk 0 1 2 3 4 5 6 7

@[expose] def tauN : Nat := pk 0 1 2 3 4 5 7 6

@[expose] def c1N : Nat := pk 1 2 0 3 4 5 6 7

@[expose] def c2N : Nat := pk 0 1 2 4 5 3 6 7

@[expose] def leaf1 (Q : Nat) : Bool :=
  !(Nat.beq (compN Q Q) idN) || Nat.beq Q idN || Nat.beq Q tauN

@[expose] def tab1 (a b c d : Nat) : Nat :=
  pk a (gN c1N a) (gN c1N (gN c1N a)) b (gN c2N b) (gN c2N (gN c2N b)) c d

@[expose] noncomputable def a8Chk1 : Bool :=
  (List.range 8).all fun a => (List.range 8).all fun b => (List.range 8).all fun c =>
    (List.range 8).all fun d => leaf1 (tab1 a b c d)

@[expose] def commN (P C : Nat) : Nat := compN (compN (compN P C) (invN P)) (invN C)

@[expose] noncomputable def leaf2 (P : Nat) : Bool :=
  !(Nat.beq (powN 7 P) idN) || Nat.beq P idN || Nat.beq P tauN ||
    !(Nat.beq (powN 7 (commN P c2N)) idN) || !(Nat.beq (powN 7 (commN P (compN c1N c2N))) idN)

@[expose] noncomputable def a8Chk2 : Bool :=
  (List.range 6).all fun a0 => (List.range 6).all fun a1 => Nat.beq a1 a0 ||
  (List.range 6).all fun a2 => Nat.beq a2 a0 || Nat.beq a2 a1 ||
  (List.range 6).all fun a3 => Nat.beq a3 a0 || Nat.beq a3 a1 || Nat.beq a3 a2 ||
  (List.range 6).all fun a4 => Nat.beq a4 a0 || Nat.beq a4 a1 || Nat.beq a4 a2 || Nat.beq a4 a3 ||
  (List.range 6).all fun a5 => Nat.beq a5 a0 || Nat.beq a5 a1 || Nat.beq a5 a2 ||
    Nat.beq a5 a3 || Nat.beq a5 a4 ||
  (List.range 2).all fun e => leaf2 (pk a0 a1 a2 a3 a4 a5 (6 + e) (7 - e))

end CFSG.KC.A8Hold

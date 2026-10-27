module

public import CFSG.LieType.SeitzGeneration.HeisSmallCheck
public import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.KC.HeisN

open CFSG.LieType.SeitzGeneration.HeisSmall

structure FK where
  p : Nat
  add : Nat → Nat → Nat
  mul : Nat → Nat → Nat
  neg : Nat → Nat

namespace FK

variable (K : FK)

@[expose] def eAdd (x y : Nat) : Nat :=
  K.add (x % K.p) (y % K.p) + K.p * K.add (x / K.p) (y / K.p)

@[expose] def eNeg (x : Nat) : Nat := K.neg (x % K.p) + K.p * K.neg (x / K.p)

@[expose] def eSub (x y : Nat) : Nat := K.eAdd x (K.eNeg y)

@[expose] def eMul (x y : Nat) : Nat :=
  let a := x % K.p
  let b := x / K.p
  let c := y % K.p
  let d := y / K.p
  let bd := K.mul b d
  K.add (K.mul a c) (K.neg bd) + K.p * K.add (K.add (K.mul a d) (K.mul b c)) (K.neg bd)

@[expose] def ePow (x : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => K.eMul (ePow x n) x

@[expose] def mMul (A B : M3 Nat) : M3 Nat :=
  ⟨K.eAdd (K.eAdd (K.eMul A.a00 B.a00) (K.eMul A.a01 B.a10)) (K.eMul A.a02 B.a20),
    K.eAdd (K.eAdd (K.eMul A.a00 B.a01) (K.eMul A.a01 B.a11)) (K.eMul A.a02 B.a21),
    K.eAdd (K.eAdd (K.eMul A.a00 B.a02) (K.eMul A.a01 B.a12)) (K.eMul A.a02 B.a22),
    K.eAdd (K.eAdd (K.eMul A.a10 B.a00) (K.eMul A.a11 B.a10)) (K.eMul A.a12 B.a20),
    K.eAdd (K.eAdd (K.eMul A.a10 B.a01) (K.eMul A.a11 B.a11)) (K.eMul A.a12 B.a21),
    K.eAdd (K.eAdd (K.eMul A.a10 B.a02) (K.eMul A.a11 B.a12)) (K.eMul A.a12 B.a22),
    K.eAdd (K.eAdd (K.eMul A.a20 B.a00) (K.eMul A.a21 B.a10)) (K.eMul A.a22 B.a20),
    K.eAdd (K.eAdd (K.eMul A.a20 B.a01) (K.eMul A.a21 B.a11)) (K.eMul A.a22 B.a21),
    K.eAdd (K.eAdd (K.eMul A.a20 B.a02) (K.eMul A.a21 B.a12)) (K.eMul A.a22 B.a22)⟩

@[expose] def mSmul (c : Nat) (A : M3 Nat) : M3 Nat :=
  ⟨K.eMul c A.a00, K.eMul c A.a01, K.eMul c A.a02, K.eMul c A.a10, K.eMul c A.a11,
    K.eMul c A.a12, K.eMul c A.a20, K.eMul c A.a21, K.eMul c A.a22⟩

@[expose] def mDet (A : M3 Nat) : Nat :=
  K.eSub (K.eAdd (K.eAdd (K.eSub (K.eSub (K.eMul (K.eMul A.a00 A.a11) A.a22)
    (K.eMul (K.eMul A.a00 A.a12) A.a21)) (K.eMul (K.eMul A.a01 A.a10) A.a22))
    (K.eMul (K.eMul A.a01 A.a12) A.a20)) (K.eMul (K.eMul A.a02 A.a10) A.a21))
    (K.eMul (K.eMul A.a02 A.a11) A.a20)

@[expose] def mPowTr (q : Nat) (A : M3 Nat) : M3 Nat :=
  ⟨K.ePow A.a00 q, K.ePow A.a10 q, K.ePow A.a20 q, K.ePow A.a01 q, K.ePow A.a11 q,
    K.ePow A.a21 q, K.ePow A.a02 q, K.ePow A.a12 q, K.ePow A.a22 q⟩

end FK

@[expose] def mOne : M3 Nat := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

@[expose] def mEq (A B : M3 Nat) : Bool :=
  Nat.beq A.a00 B.a00 && Nat.beq A.a01 B.a01 && Nat.beq A.a02 B.a02 && Nat.beq A.a10 B.a10 &&
    Nat.beq A.a11 B.a11 && Nat.beq A.a12 B.a12 && Nat.beq A.a20 B.a20 && Nat.beq A.a21 B.a21 &&
    Nat.beq A.a22 B.a22

@[expose] def matN (l : List Nat) : M3 Nat :=
  ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0,
    l.getD 7 0, l.getD 8 0⟩

namespace FK

variable (K : FK)

@[expose] def linesN (w : Nat) : List (M3 Nat) :=
  let d : M3 Nat := ⟨1, 0, 0, 0, w, 0, 0, 0, K.ePow w 2⟩
  let s : M3 Nat := ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩
  [d, s, K.mMul d s, K.mMul (K.mMul d s) s]

@[expose] def cGuess (P Q : M3 Nat) : Nat :=
  match ([(P.a00, Q.a00), (P.a01, Q.a01), (P.a02, Q.a02), (P.a10, Q.a10), (P.a11, Q.a11),
      (P.a12, Q.a12), (P.a20, Q.a20), (P.a21, Q.a21), (P.a22, Q.a22)].find?
      fun e => !Nat.beq e.2 0) with
  | some e => ((List.range (K.p * K.p)).find? fun x => Nat.beq (K.eMul x e.2) e.1).getD 0
  | none => 0

@[expose] def genOkN (q w : Nat) (G : M3 Nat) : Bool :=
  Nat.beq (K.mDet G) 1 && mEq (K.mMul (K.mPowTr q G) G) mOne &&
    (K.linesN w).any fun M =>
      let P := K.mMul G M
      let Q := K.mMul M G
      mEq P (K.mSmul (K.cGuess P Q) Q)

@[expose] def evalN (letters : List (M3 Nat)) : List Nat → M3 Nat
  | [] => mOne
  | i :: w => K.mMul (letters.getD i mOne) (evalN letters w)

@[expose] def keyN (q : Nat) (V : M3 Nat) : Option Nat :=
  if Nat.blt V.a00 (K.p * K.p) && Nat.blt V.a01 (K.p * K.p) && Nat.beq V.a02 0 &&
      Nat.beq V.a10 (K.eNeg (K.ePow V.a01 q)) && Nat.beq V.a11 (K.ePow V.a00 q) &&
      Nat.beq V.a12 0 && Nat.beq V.a20 0 && Nat.beq V.a21 0 && Nat.beq V.a22 1 then
    some (V.a00 + K.p * K.p * V.a01)
  else none

@[expose] def bitsN (q : Nat) : List (M3 Nat) → Nat
  | [] => 0
  | V :: vs =>
    match K.keyN q V with
    | some k => bitsN q vs ||| (1 <<< k)
    | none => bitsN q vs

@[expose] def coverN (q : Nat) (vals : List (M3 Nat)) : Bool :=
  let n := K.p * K.p
  let bits := K.bitsN q vals
  let nt := (List.range n).map fun a => (a, K.eMul a (K.ePow a q))
  nt.all fun x => nt.all fun y => !Nat.beq (K.eAdd x.2 y.2) 1 || bits.testBit (x.1 + n * y.1)

@[expose] def heisN (q w : Nat) (raw : List (List Nat)) (ws₁ ws₂ : List (List Nat)) : Bool :=
  let gens := raw.map matN
  gens.all (K.genOkN q w) && K.coverN q (ws₂.map (K.evalN (ws₁.map (K.evalN gens))))

end FK

@[expose] def fkP (p : Nat) : FK := ⟨p, fun a b => (a + b) % p, fun a b => a * b % p,
  fun a => (p - a % p) % p⟩

end CFSG.KC.HeisN

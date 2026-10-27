module

public section

namespace CFSG.LieType.Chevalley.C2E6Std.MatrixModel.Native

abbrev Vec := Nat × Nat

abbrev Mat := Array Vec

@[expose] def vadd (u v : Vec) : Vec := (u.1 ^^^ v.1, u.2 ^^^ v.2)

@[expose] def vsmul (c0 c1 : Bool) (v : Vec) : Vec :=
  ((if c0 then v.1 else 0) ^^^ (if c1 then v.2 else 0),
    (if c0 then v.2 else 0) ^^^ (if c1 then v.1 ^^^ v.2 else 0))

@[expose] def applyAux (P : Mat) (u : Vec) : Nat → Vec → Vec
  | 0, acc => acc
  | n + 1, acc =>
    vadd (applyAux P u n acc) (vsmul (u.1.testBit n) (u.2.testBit n) (P.getD n (0, 0)))

@[expose] def apply (P : Mat) (u : Vec) : Vec := applyAux P u 78 (0, 0)

@[expose] def mul (P Q : Mat) : Mat := Q.map (apply P)

@[expose] def one (_ : Unit := ()) : Mat := (List.range 78).toArray.map fun l => (1 <<< l, 0)

@[expose] def pow (P : Mat) : Nat → Mat
  | 0 => one
  | n + 1 => mul (pow P n) P

@[expose] def code (codes a b : Nat) : Nat := (codes >>> (8 * (78 * a + b))) % 256

@[expose] def maskOf (e : Nat) : Nat := if e < 64 then e else 1 <<< (e - 58)

@[expose] def fbit (bits a b : Nat) : Bool := bits.testBit (78 * a + b)

@[expose] def rootCol (codes bits r : Nat) (c0 c1 : Bool) (l : Nat) : Vec :=
  vadd (vadd (1 <<< l, 0) (vsmul c0 c1 (maskOf (code codes r l), 0)))
    (if fbit bits r l then vsmul (c0 ^^ c1) c1 (1 <<< r, 0) else (0, 0))

@[expose] def rootMat (codes bits r : Nat) (c0 c1 : Bool) : Mat :=
  (List.range 78).toArray.map (rootCol codes bits r c0 c1)

@[expose] def xMat (codes bits j : Nat) (c0 c1 : Bool) : Mat := rootMat codes bits (6 + j) c0 c1

@[expose] def yMat (codes bits j : Nat) : Mat := rootMat codes bits (12 + 2 * j) true false

@[expose] def nMat (codes bits j : Nat) : Mat :=
  mul (mul (xMat codes bits j true false) (yMat codes bits j)) (xMat codes bits j true false)

@[expose] def letters (codes bits : Nat) : Array Mat :=
  let x := xMat codes bits
  let n := nMat codes bits
  #[mul (x 0 true false) (x 5 true false), mul (x 0 false true) (x 5 true true),
    mul (x 0 true true) (x 5 false true), mul (x 2 true false) (x 4 true false),
    mul (x 2 false true) (x 4 true true), mul (x 2 true true) (x 4 false true),
    x 3 true false, x 1 true false, mul (n 0) (n 5), mul (n 2) (n 4), n 3, n 1]

@[expose] def lineProd (vals : Array Mat) (line : List Nat) : Mat :=
  line.foldl (fun acc i => mul acc (vals.getD i one)) one

@[expose] def slpRun (gens : Array Mat) (prog : List (List Nat)) : Array Mat :=
  prog.foldl (fun vals line => vals.push (lineProd vals line)) gens

@[expose] def genAB (codes bits : Nat) (fwd : List (List Nat)) (iA iB : Nat) : Mat × Mat :=
  let F := slpRun (letters codes bits) fwd
  (F.getD iA one, F.getD iB one)

@[expose] def eqM (P Q : Mat) : Bool :=
  (List.range 78).all fun l => (List.range 78).all fun k =>
    (P.getD l (0, 0)).1.testBit k == (Q.getD l (0, 0)).1.testBit k &&
      (P.getD l (0, 0)).2.testBit k == (Q.getD l (0, 0)).2.testBit k

@[expose] def ordP (P : Mat) (p : Nat) : Bool := eqM (pow P p) one && !eqM P one

@[expose] def check (codes bits : Nat) (fwd : List (List Nat)) (iA iB : Nat)
    (bwd : List (List Nat)) (tgt : List Nat) : Bool :=
  let L := letters codes bits
  let AB := genAB codes bits fwd iA iB
  let V := slpRun #[AB.1, AB.2] bwd
  (List.range 12).all (fun j => eqM (V.getD (tgt.getD j 0) one) (L.getD j one)) &&
    ordP AB.1 2 && ordP AB.2 3 && ordP (mul AB.1 AB.2) 19

@[expose] def signedMat (A B : Mat) (l : Nat × Bool) : Mat :=
  if l.1 = 0 then A else if l.2 then B else mul B B

@[expose] def wordMat (A B : Mat) (w : List (Nat × Bool)) : Mat :=
  w.foldl (fun acc l => mul acc (signedMat A B l)) one

@[expose] def relCheck (codes bits : Nat) (fwd : List (List Nat)) (iA iB : Nat)
    (ws : List (List (Nat × Bool))) : Bool :=
  let AB := genAB codes bits fwd iA iB
  eqM (mul AB.1 AB.1) one && eqM (mul (mul AB.2 AB.2) AB.2) one &&
    ws.all fun w => eqM (wordMat AB.1 AB.2 w) one

end CFSG.LieType.Chevalley.C2E6Std.MatrixModel.Native

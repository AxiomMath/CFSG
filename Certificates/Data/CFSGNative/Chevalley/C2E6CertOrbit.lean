module

public import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public import Std.Data.HashMap

public section

namespace CFSG.Monster.Existence.StdOdd.CertNative

open CFSG.LieType.Chevalley.C2E6Std.MatrixModel.Native

@[expose] def e7 : Vec := (1 <<< 7, 0)

structure OrbitCert where
  pts : Array Vec
  par : Array Nat
  gen : Array Bool
  nbA : Array Nat
  nbB : Array Nat
  idx : Vec → Nat

def produce (A B : Mat) (e : Vec) : OrbitCert := Id.run do
  let TA := mkTbl A
  let TB := mkTbl B
  let mut pts : Array Vec := #[e]
  let mut par : Array Nat := #[0]
  let mut gen : Array Bool := #[false]
  let mut nbA : Array Nat := #[]
  let mut nbB : Array Nat := #[]
  let mut tbl : Std.HashMap Vec Nat := (∅ : Std.HashMap Vec Nat).insert e 0
  let mut h := 0
  while h < pts.size do
    let u := pts[h]!
    let wa := applyT TA u
    match tbl.get? wa with
    | some j => nbA := nbA.push j
    | none =>
      let j := pts.size
      pts := pts.push wa
      par := par.push h
      gen := gen.push false
      tbl := tbl.insert wa j
      nbA := nbA.push j
    let wb := applyT TB u
    match tbl.get? wb with
    | some j => nbB := nbB.push j
    | none =>
      let j := pts.size
      pts := pts.push wb
      par := par.push h
      gen := gen.push true
      tbl := tbl.insert wb j
      nbB := nbB.push j
    h := h + 1
  return ⟨pts, par, gen, nbA, nbB, fun v => tbl.getD v 0⟩

@[inline, expose] def allStep (j c n : Nat) (p : Nat → Bool) : Bool :=
  Nat.all ((n + c - 1 - j) / c) fun k _ => p (j + c * k)

@[expose] def parAll (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let c := chunks + 1
  ((List.range c).map fun j => Task.spawn fun _ => allStep j c n p).all Task.get

@[expose] def verifyAt (TA TB : Array Vec) (c : OrbitCert) (i : Nat) : Bool :=
  let n := c.pts.size
  let u := c.pts.getD i (0, 0)
  let a := c.nbA.getD i n
  let b := c.nbB.getD i n
  isCanon u && c.idx u == i && a < n && b < n &&
    c.pts.getD a (0, 0) == applyT TA u && c.pts.getD b (0, 0) == applyT TB u &&
    (i == 0 ||
      (let p := c.par.getD i i
       p < i && (if c.gen.getD i false then c.nbB.getD p n else c.nbA.getD p n) == i))

@[expose] def verify (A B : Mat) (e : Vec) (c : OrbitCert) (chunks : Nat) : Bool :=
  let TA := mkTbl A
  let TB := mkTbl B
  0 < c.pts.size && c.pts.getD 0 (0, 0) == e && parAll c.pts.size chunks (verifyAt TA TB c)

@[expose] def OrbitCert.mem (c : OrbitCert) (u : Vec) : Bool :=
  c.idx u < c.pts.size && c.pts.getD (c.idx u) (0, 0) == u

@[expose] def orbitCheck (A B : Mat) (chunks n : Nat) : Bool :=
  let c := produce A B e7
  verify A B e7 c chunks && c.pts.size == n

@[expose] def orbitCheckAB (codes bits : Nat) (fwd : List (List Nat)) (iA iB chunks n : Nat) :
    Bool :=
  let AB := genAB codes bits fwd iA iB
  orbitCheck AB.1 AB.2 chunks n

@[expose] def withOrbit (A B : Mat) (chunks : Nat) (f : OrbitCert → Bool) : Bool :=
  let c := produce A B e7
  verify A B e7 c chunks && f c

@[expose] def rhoWith (fm : Vec → Vec → Bool × Bool) (bnz : Vec → Vec → Bool) (mem : Vec → Bool)
    (u w : Vec) : Nat :=
  if u == w then 0 else
    let b := fm u w
    if b.1 || b.2 then 4 else if bnz u w then 3 else if mem (vadd u w) then 1 else 2

@[expose] def rhoN (ps : List (Nat × Nat)) (ts : List (Nat × Nat × Nat)) (mem : Vec → Bool)
    (u w : Vec) : Nat :=
  rhoWith (bform ps) (fun u w => let c := bracket ts u w; c.1 != 0 || c.2 != 0) mem u w

@[expose] def rhoT (TF : Array Vec) (BO : Array (List (Nat × Nat))) (mem : Vec → Bool)
    (u w : Vec) : Nat :=
  rhoWith (bformT TF) (bracketNZ BO) mem u w

end CFSG.Monster.Existence.StdOdd.CertNative

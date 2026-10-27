module

public import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix

public section

namespace CFSG.Monster.Existence.StdOdd.CertNative

open CFSG.LieType.Chevalley.C2E6Std.MatrixModel.Native

@[inline, expose] def isCanon (u : Vec) : Bool := u.1 < 2 ^ 78 && u.2 < 2 ^ 78

@[inline, expose] def f4mul (a₀ a₁ c₀ c₁ : Bool) : Bool × Bool :=
  ((a₀ && c₀) ^^ (a₁ && c₁), (a₀ && c₁) ^^ (a₁ && (c₀ ^^ c₁)))

@[expose] def pairsWhere (P : Nat → Nat → Bool) : List (Nat × Nat) :=
  (List.range 78).flatMap fun a => ((List.range 78).filter fun b => P a b).map fun b => (a, b)

@[expose] def formPairs (bits : Nat) : List (Nat × Nat) := pairsWhere (fbit bits)

@[inline, expose] def bformStep (u w : Vec) (acc : Bool × Bool) (p : Nat × Nat) : Bool × Bool :=
  let t := f4mul (u.1.testBit p.1) (u.2.testBit p.1) (w.1.testBit p.2) (w.2.testBit p.2)
  (acc.1 ^^ t.1, acc.2 ^^ t.2)

@[expose] def bform (ps : List (Nat × Nat)) (u w : Vec) : Bool × Bool :=
  ps.foldl (bformStep u w) (false, false)

@[expose] def brTriples (codes : Nat) : List (Nat × Nat × Nat) :=
  (List.range 78).flatMap fun a => (List.range 78).filterMap fun b =>
    if maskOf (code codes a b) == 0 then none else some (a, b, maskOf (code codes a b))

@[inline, expose] def bracketStep (u w : Vec) (acc : Vec) (t : Nat × Nat × Nat) : Vec :=
  let p := f4mul (u.1.testBit t.1) (u.2.testBit t.1) (w.1.testBit t.2.1) (w.2.testBit t.2.1)
  if p.1 || p.2 then vadd acc (vsmul p.1 p.2 (t.2.2, 0)) else acc

@[expose] def bracket (ts : List (Nat × Nat × Nat)) (u w : Vec) : Vec :=
  ts.foldl (bracketStep u w) (0, 0)

@[expose] def brOut (codes : Nat) : Array (List (Nat × Nat)) :=
  Array.ofFn (n := 78) fun k => pairsWhere fun a b => (maskOf (code codes a b)).testBit k

@[expose] def bracketNZ (BO : Array (List (Nat × Nat))) (u w : Vec) : Bool :=
  (List.range 78).any fun k =>
    let r := bform (BO.getD k []) u w
    r.1 || r.2

@[expose] def matCanonB (P : Mat) : Bool :=
  (List.range 78).all fun l => isCanon (P.getD l (0, 0))

@[expose] def matCanonAB (codes bits : Nat) (fwd : List (List Nat)) (iA iB : Nat) : Bool :=
  let AB := genAB codes bits fwd iA iB
  matCanonB AB.1 && matCanonB AB.2

@[expose] def tblEntry (P : Mat) (c m : Nat) : Vec :=
  (List.range 8).foldl (fun acc j =>
    if m.testBit j && 8 * c + j < 78 then vadd acc (P.getD (8 * c + j) (0, 0)) else acc) (0, 0)

@[expose] def mkTbl (P : Mat) : Array Vec :=
  Array.ofFn (n := 2560) fun i => tblEntry P (i.val / 256) (i.val % 256)

@[expose] def selAux (T : Array Vec) : Nat → Nat → Nat → Vec → Vec
  | 0, _, _, acc => acc
  | n + 1, c, x, acc =>
    selAux T n (c + 1) (x >>> 8) (vadd acc (T.getD (256 * c + (x &&& 255)) (0, 0)))

@[expose] def selT (T : Array Vec) (x : Nat) : Vec := selAux T 10 0 x (0, 0)

@[expose] def applyT (T : Array Vec) (u : Vec) : Vec :=
  let A := selT T u.1
  let B := selT T u.2
  (A.1 ^^^ B.2, A.2 ^^^ B.1 ^^^ B.2)

@[expose] def formMat (bits : Nat) : Mat :=
  Array.ofFn (n := 78) fun b =>
    ((List.range 78).foldl (fun m a => if fbit bits a b then m ||| (1 <<< a) else m) 0, 0)

@[expose] def par8 (m : Nat) : Bool :=
  let a := m ^^^ (m >>> 4)
  let b := a ^^^ (a >>> 2)
  (b ^^^ (b >>> 1)) &&& 1 == 1

@[expose] def parAux : Nat → Nat → Bool → Bool
  | 0, _, acc => acc
  | n + 1, x, acc => parAux n (x >>> 8) (acc ^^ par8 (x &&& 255))

@[expose] def parity (x : Nat) : Bool := parAux 10 x false

@[expose] def dotBits (u v : Vec) : Bool × Bool :=
  (parity ((u.1 &&& v.1) ^^^ (u.2 &&& v.2)),
    parity ((u.1 &&& v.2) ^^^ (u.2 &&& v.1) ^^^ (u.2 &&& v.2)))

@[expose] def bformT (TF : Array Vec) (u w : Vec) : Bool × Bool := dotBits u (applyT TF w)

end CFSG.Monster.Existence.StdOdd.CertNative

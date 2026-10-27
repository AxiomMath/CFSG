module

public section

set_option compiler.extract_closed false

namespace CFSG.ClassicalInvolution.PhanDn.D4Q2

@[expose] def mul4 : Nat → Nat → Nat
  | 1, b => b
  | 2, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 1
  | 3, 1 => 3
  | 3, 2 => 1
  | 3, 3 => 2
  | _, _ => 0

@[expose] def frob4 : Nat → Nat
  | 2 => 3
  | 3 => 2
  | a => a

@[expose] def cd (v k : Nat) : Nat := (v >>> (2 * k)) % 4

@[expose] def quadC (v : Nat) : Nat :=
  mul4 (cd v 0) (cd v 4) ^^^ mul4 (cd v 1) (cd v 5) ^^^ mul4 (cd v 2) (cd v 6) ^^^
    mul4 (cd v 3) (cd v 7)

@[expose] def polarC (u v : Nat) : Nat :=
  mul4 (cd u 0) (cd v 4) ^^^ mul4 (cd u 4) (cd v 0) ^^^ mul4 (cd u 1) (cd v 5) ^^^
    mul4 (cd u 5) (cd v 1) ^^^ mul4 (cd u 2) (cd v 6) ^^^ mul4 (cd u 6) (cd v 2) ^^^
    mul4 (cd u 3) (cd v 7) ^^^ mul4 (cd u 7) (cd v 3)

@[expose] def hermC (u v : Nat) : Nat :=
  mul4 (cd u 0) (frob4 (cd v 0)) ^^^ mul4 (cd u 1) (frob4 (cd v 1)) ^^^
    mul4 (cd u 2) (frob4 (cd v 2)) ^^^ mul4 (cd u 3) (frob4 (cd v 3)) ^^^
    mul4 (cd u 4) (frob4 (cd v 4)) ^^^ mul4 (cd u 5) (frob4 (cd v 5)) ^^^
    mul4 (cd u 6) (frob4 (cd v 6)) ^^^ mul4 (cd u 7) (frob4 (cd v 7))

@[expose] def smulC (a v : Nat) : Nat :=
  mul4 a (cd v 0) + 4 * mul4 a (cd v 1) + 16 * mul4 a (cd v 2) + 64 * mul4 a (cd v 3) +
    256 * mul4 a (cd v 4) + 1024 * mul4 a (cd v 5) + 4096 * mul4 a (cd v 6) +
    16384 * mul4 a (cd v 7)

@[expose] def normC (v : Nat) : Bool :=
  match (List.range 8).find? fun k => cd v k != 0 with
  | some k => cd v k == 1
  | none => false

@[expose] def ptAdjC (u v : Nat) : Bool := u != v && polarC u v == 0 && hermC u v == 0

@[expose] def memC (P : Array Nat) (fr : Array Nat) (v : Nat) : Bool :=
  let b0 := P[fr[0]!]!
  let b1 := P[fr[1]!]!
  let b2 := P[fr[2]!]!
  let b3 := P[fr[3]!]!
  v == (smulC (hermC v b0) b0 ^^^ smulC (hermC v b1) b1 ^^^ smulC (hermC v b2) b2 ^^^
    smulC (hermC v b3) b3)

@[expose] def ptCodes (_ : Unit := ()) : Array Nat :=
  (Array.range 65536).filter fun v => normC v && quadC v == 0 && hermC v v != 0

@[noinline, expose] def solFramesOf (P : Array Nat) : Array (Array Nat) := Id.run do
  let n := P.size
  let A : Array (Array Nat) :=
    (Array.range n).map fun i => (Array.range n).filter fun i' => ptAdjC P[i]! P[i']!
  let mut F : Array (Array Nat) := #[]
  let mut I : Array (Array Bool) := #[]
  let mut S : Array (Array Nat) := Array.replicate n #[]
  for i1 in [0:n] do
    for i2 in A[i1]! do
      if i1 < i2 then
        let C := (A[i1]!).filter fun i3 => i2 < i3 && ptAdjC P[i2]! P[i3]!
        for i3 in C do
          for i4 in C do
            if i3 < i4 && ptAdjC P[i3]! P[i4]! then
              let known := (S[i1]!).any fun j => (I[j]!)[i2]! && (I[j]!)[i3]! && (I[j]!)[i4]!
              if !known then
                let fr := #[i1, i2, i3, i4]
                let row := (Array.range n).map fun i => memC P fr P[i]!
                let j := F.size
                F := F.push fr
                I := I.push row
                for i in [0:n] do
                  if row[i]! then
                    S := S.modify i (·.push j)
  return F

@[expose] def solFrames (_ : Unit := ()) : Array (Array Nat) := solFramesOf (ptCodes ())

structure Tabs where
  pts : Array Nat
  frames : Array (Array Nat)
  inc : Array (Array Bool)
  solPts : Array (Array Nat)

@[noinline, expose] def mkTabs (P : Array Nat) (F : Array (Array Nat)) : Tabs :=
  let I := F.map fun fr => (Array.range P.size).map fun i => memC P fr P[i]!
  ⟨P, F, I, I.map fun r => (Array.range r.size).filter fun i => r[i]!⟩

@[expose] def tabs (_ : Unit := ()) : Tabs := mkTabs (ptCodes ()) (solFrames ())

@[expose] def commonPts (T : Tabs) (j j' : Nat) : Array Nat :=
  (T.solPts[j]!).filter fun a => (T.inc[j']!)[a]!

@[expose] def triTest (T : Tabs) (j j' : Nat) : Bool :=
  let C := commonPts T j j'
  C.any fun a => C.any fun b => C.any fun c =>
    ptAdjC T.pts[a]! T.pts[b]! && ptAdjC T.pts[a]! T.pts[c]! && ptAdjC T.pts[b]! T.pts[c]!

@[expose] def adjT (T : Tabs) (x y : Nat) : Bool :=
  if x < 2240 then
    if y < 2240 then ptAdjC T.pts[x]! T.pts[y]! else (T.inc[y - 2240]!)[x]!
  else
    if y < 2240 then (T.inc[x - 2240]!)[y]! else x != y && triTest T (x - 2240) (y - 2240)

@[noinline, expose] def nbOf (T : Tabs) : Array (Array Nat) :=
  (Array.range 6720).map fun x => (Array.range 6720).filter (adjT T x)

@[expose] def nb (_ : Unit := ()) : Array (Array Nat) := nbOf (tabs ())

@[expose] def sizeCheck (T : Tabs) : Bool := T.pts.size == 2240 && T.frames.size == 4480

@[expose] def frameCheck (T : Tabs) : Bool :=
  T.frames.all fun fr => fr.size == 4 && fr.all (· < 2240) &&
    ptAdjC T.pts[fr[0]!]! T.pts[fr[1]!]! && ptAdjC T.pts[fr[0]!]! T.pts[fr[2]!]! &&
    ptAdjC T.pts[fr[0]!]! T.pts[fr[3]!]! && ptAdjC T.pts[fr[1]!]! T.pts[fr[2]!]! &&
    ptAdjC T.pts[fr[1]!]! T.pts[fr[3]!]! && ptAdjC T.pts[fr[2]!]! T.pts[fr[3]!]!

@[expose] def distinctCheck (T : Tabs) : Bool :=
  (List.range 4480).all fun j => (List.range j).all fun j' => T.solPts[j]! != T.solPts[j']!

@[expose] def cliqueCheck (T : Tabs) : Bool :=
  let A := (Array.range 2240).map fun i =>
    (Array.range 2240).filter fun i' => ptAdjC T.pts[i]! T.pts[i']!
  let S := (Array.range 2240).map fun i => (Array.range 4480).filter fun j => (T.inc[j]!)[i]!
  (List.range 2240).all fun i1 => (A[i1]!).all fun i2 => !(i1 < i2) ||
    let C := (A[i1]!).filter fun i3 => i2 < i3 && ptAdjC T.pts[i2]! T.pts[i3]!
    C.all fun i3 => (C.filter fun i4 => i3 < i4 && ptAdjC T.pts[i3]! T.pts[i4]!).all fun i4 =>
      (S[i1]!).any fun j => (T.inc[j]!)[i2]! && (T.inc[j]!)[i3]! && (T.inc[j]!)[i4]!

@[expose] def apartCheck (T : Tabs) : Bool :=
  (List.range 4480).all fun j => (List.range 4480).all fun j' => j == j' || triTest T j j' ||
    (T.solPts[j]!).any fun a => (T.solPts[j]!).any fun b =>
      let u := T.pts[a]!
      let v := T.pts[b]!
      !(T.inc[j']!)[a]! && !(T.inc[j']!)[b]! && !memC T.pts (T.frames[j']!) (u ^^^ v) &&
        !memC T.pts (T.frames[j']!) (u ^^^ smulC 2 v) &&
        !memC T.pts (T.frames[j']!) (u ^^^ smulC 3 v)

end CFSG.ClassicalInvolution.PhanDn.D4Q2

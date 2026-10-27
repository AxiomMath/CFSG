module

public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public import Certificates.Data.CFSGNative.Fi23.Classes
public import Certificates.Data.CFSGNative.Fi23.Centralizer

public section

namespace CFSG.Monster.Existence.Fi23Sp8.Native

open CFSG.Sporadic.Bridge.Fi23GPL.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def gIdx (_ : Unit := ()) : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 9]

@[inline, expose] def letterOK (z : Int) : Bool := 1 ≤ z && z ≤ 10 && z != 9

@[inline, expose] def sLetterOK (z : Int) : Bool := letterOK z || letterOK (-z)

@[expose] def invWord (w : List Int) : List Int := w.reverse.map fun z => -z

@[inline, expose] def evalWord (I Iv : Array Table) (w : List Int) (q : Nat) : Nat :=
  w.foldr (fun z x => ap (imgLetter I Iv z) x) q

@[expose] def dPow (_ : Unit := ()) : List Int := (List.replicate 7 dLetters).flatten

@[expose] def prefLen (k : Nat) : Nat := (imgWords[k]!.length - 84) / 2

@[expose] def prefWord (k : Nat) : List Int := imgWords[k]!.take (prefLen k)

@[expose] def piPt (G4 : Array Table) (k : Nat) : Nat :=
  ap (wordT 31671 (seedLetter G4) (prefWord k)) 0

@[expose] def imgConjOK (_ : Unit := ()) : Bool :=
  imgWords.size == 10 &&
    (List.range 10).all fun k =>
      imgWords[k]! == prefWord k ++ dPow ++ invWord (prefWord k) &&
        (prefWord k).all fun z => z == 1 || z == -1 || z == 2 || z == -2

structure Search where
  roots : Array Nat
  lab : Array Nat
  par : Array Nat
  gen : Array Nat
  vec : Array Nat
  ptOf : Array Nat

@[expose] def pathWord (par gen : Array Nat) (r : Nat) : Nat → Nat → List Int
  | 0, _ => []
  | f + 1, p => if p == r then [] else ((gen[p]! + 1 : Nat) : Int) :: pathWord par gen r f par[p]!

@[expose] def pathW (S : Search) (p : Nat) : List Int :=
  pathWord S.par S.gen S.roots[S.lab[p]!]! 100 p

@[expose] def conjAct (I Iv : Array Table) (u : List Int) (q : Nat) : Nat :=
  evalWord I Iv u (ap I[0]! (evalWord I Iv (invWord u) q))

@[expose] def commPt (I Iv : Array Table) (S : Search) (p q : Nat) : Bool :=
  conjAct I Iv (pathW S p) q == q

@[expose] def sigList (S : Search) : List Nat :=
  (List.range 31671).filter fun p => S.lab[p]! == 0

@[expose] def orbSearch (I : Array Table) (roots : List Nat) : Array Nat × Array Nat × Array Nat :=
  Id.run do
    let n := 31671
    let mut lab : Array Nat := Array.replicate n 3
    let mut par : Array Nat := Array.replicate n 0
    let mut gen : Array Nat := Array.replicate n 0
    let mut c := 0
    for r in roots do
      if lab[r]! == 3 then
        lab := lab.set! r c
        let mut q : Array Nat := #[r]
        let mut h := 0
        for _ in [0:n] do
          if h < q.size then
            let p := q[h]!
            h := h + 1
            for k in gIdx do
              let y := ap I[k]! p
              if lab[y]! == 3 then
                lab := lab.set! y c
                par := par.set! y p
                gen := gen.set! y k
                q := q.push y
          else break
      c := c + 1
    return (lab, par, gen)

@[expose] def chooseBasis (comm : Nat → Nat → Bool) (sig : List Nat) : Array Nat := Id.run do
  let mut chosen : Array Nat := #[]
  let mut b : Array Nat := Array.replicate 8 0
  for i in [0:4] do
    let c1 := (sig.find? fun p => !chosen.contains p && chosen.all fun c => comm p c).getD 0
    chosen := chosen.push c1
    b := b.set! i c1
    let c2 := (sig.find? fun p =>
      !chosen.contains p && !comm p c1 && chosen.all fun c => c == c1 || comm p c).getD 0
    chosen := chosen.push c2
    b := b.set! (4 + i) c2
  return b

@[expose] def vecOfPt (comm : Nat → Nat → Bool) (b : Array Nat) (x : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:4] do
    if !comm b[4 + i]! x then v := v ||| (1 <<< i)
    if !comm b[i]! x then v := v ||| (1 <<< (4 + i))
  return v

@[expose] def search (G4 I Iv : Array Table) : Search :=
  let roots : Array Nat := #[piPt G4 0, piPt G4 8, 0]
  let t := orbSearch I roots.toList
  let S0 : Search := ⟨roots, t.1, t.2.1, t.2.2, #[], #[]⟩
  let sig := sigList S0
  let b := chooseBasis (commPt I Iv S0) sig
  let vecs : Array Nat := Array.ofFn (n := 31671) fun p =>
    if S0.lab[p.val]! == 0 then vecOfPt (commPt I Iv S0) b p.val else 0
  let ptOf : Array Nat := Id.run do
    let mut r : Array Nat := Array.replicate 256 0
    for p in sig do
      r := r.set! vecs[p]! p
    return r
  { S0 with vec := vecs, ptOf := ptOf }

@[inline, expose] def beta (u v : Nat) : Bool :=
  xor (xor (xor (u.testBit 0 && v.testBit 4) (u.testBit 4 && v.testBit 0))
        (xor (u.testBit 1 && v.testBit 5) (u.testBit 5 && v.testBit 1)))
    (xor (xor (u.testBit 2 && v.testBit 6) (u.testBit 6 && v.testBit 2))
        (xor (u.testBit 3 && v.testBit 7) (u.testBit 7 && v.testBit 3)))

@[expose] def rootCheck (G4 : Array Table) (S : Search) : Bool :=
  S.roots == #[piPt G4 0, piPt G4 8, 0] && S.lab.size == 31671 && S.par.size == 31671 &&
    S.gen.size == 31671 && (List.range 3).all fun c => S.lab[S.roots[c]!]! == c

@[expose] def labCheck (G4 I : Array Table) (S : Search) : Bool :=
  allIn 0 31671 (fun p => S.lab[p]! < 3 &&
    gIdx.all fun k => S.lab[ap I[k]! p]! == S.lab[p]!) &&
    gIdx.all fun k => S.lab[piPt G4 k]! == 0

@[expose] def pathCheck (I Iv : Array Table) (S : Search) : Bool :=
  allIn 0 31671 fun p =>
    evalWord I Iv (pathW S p) S.roots[S.lab[p]!]! == p && (pathW S p).all letterOK

@[expose] def vecCheck (S : Search) : Bool :=
  S.vec.size == 31671 && S.ptOf.size == 256 &&
    (sigList S).all (fun p => 1 ≤ S.vec[p]! && S.vec[p]! ≤ 255 && S.ptOf[S.vec[p]!]! == p) &&
    allIn 1 256 fun v => S.ptOf[v]! < 31671 && S.lab[S.ptOf[v]!]! == 0 && S.vec[S.ptOf[v]!]! == v

@[expose] def transCheck (I Iv : Array Table) (S : Search) : Bool :=
  let sig := sigList S
  sig.all fun p =>
    sig.all fun q =>
      S.vec[conjAct I Iv (pathW S p) q]! ==
        (S.vec[q]! ^^^ (if beta S.vec[p]! S.vec[q]! then S.vec[p]! else 0))

@[expose] def stabWord (I : Array Table) (S : Search) (c : Nat) (pr : Nat × Nat) : List Int :=
  invWord (pathWord S.par S.gen S.roots[c]! 100 (ap I[pr.2]! pr.1)) ++ [((pr.2 + 1 : Nat) : Int)] ++
    pathWord S.par S.gen S.roots[c]! 100 pr.1

@[expose] def stabPairs (c : Nat) : List (Nat × Nat) :=
  match c with
  | 0 => [(10724, 0), (2632, 5), (28414, 9), (11341, 1), (1382, 9), (2821, 3), (15779, 7)]
  | 1 => [(11259, 1), (16522, 2), (30086, 5), (16663, 0)]
  | _ => [(17849, 5), (26755, 1), (31093, 4)]

@[expose] def sepCheck (I Iv : Array Table) (S : Search) : Bool :=
  let sig := sigList S
  (List.range 3).all fun c =>
    let ws := (stabPairs c).map (stabWord I S c)
    ws.all (fun w => w.all sLetterOK && evalWord I Iv w S.roots[c]! == S.roots[c]!) &&
    allIn 0 31671 fun y =>
      (!(sig.all fun p => commPt I Iv S p y == commPt I Iv S p S.roots[c]!) || S.lab[y]! == c) &&
      (!(S.lab[y]! == c && ws.all fun w => evalWord I Iv w y == y) || y == S.roots[c]!)

@[expose] def orbitSize (c : Nat) : Nat :=
  match c with
  | 0 => 255
  | 1 => 13056
  | _ => 18360

@[expose] def countCheck (S : Search) : Bool :=
  (List.range 3).all fun c => (List.range 31671).countP (fun p => S.lab[p]! == c) == orbitSize c

@[expose] def genCheck (D : Table) (S : Search) : Bool :=
  S.lab[0]! == 2 && S.lab[2]! == 2 && S.lab[ap D 2]! == 1

@[expose] def sp8Checks (G4 I Iv : Array Table) (D : Table) (S : Search) : Bool :=
  imgConjOK && rootCheck G4 S && labCheck G4 I S && pathCheck I Iv S && vecCheck S &&
    transCheck I Iv S && sepCheck I Iv S && genCheck D S && countCheck S

@[noinline, expose] def sp8Run (G4 I Iv : Array Table) (D : Table) : Bool :=
  sp8Checks G4 I Iv D (search G4 I Iv)

@[noinline, expose] def sp8Inv (G4 I : Array Table) (D : Table) : Bool :=
  sp8Run G4 I (I.map (invT 31671)) D

@[noinline, expose] def sp8Tab (G4 : Array Table) (D : Table) : Bool :=
  sp8Inv G4 (imgWords.map (wordT 31671 (seedLetter G4))) D

@[noinline, expose] def sp8FromOrbit (O : WOrbit) : Bool :=
  sp8Tab #[O.alpha, O.alpha, O.beta, invT 31671 O.beta] (dTable O)

@[expose] def sp8Entry (_ : Unit) : Bool := sp8FromOrbit (orbitData ())

end CFSG.Monster.Existence.Fi23Sp8.Native

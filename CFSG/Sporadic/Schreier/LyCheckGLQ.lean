module

public import CFSG.Sporadic.Schreier.LyCheckSylow

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

set_option compiler.extract_closed false

@[inline, expose] def pickY (y : Nat × Nat × Nat) (k : Nat) : Nat :=
  if k = 0 then y.1 else if k = 1 then y.2.1 else y.2.2

@[expose] def evalY (T : Array (Array Nat)) (y : Nat × Nat × Nat) (w : List Nat) : Nat :=
  w.foldr (fun k acc => tm T (pickY y k) acc) 0

@[expose] def glqGens : Nat × Nat × Nat := (1, 3, 5)

@[expose] def glqWords (T : Array (Array Nat)) : Array (List Nat) := Id.run do
  let mut W : Array (Option (List Nat)) := (Array.replicate 256 none).set! 0 (some [])
  let mut q : Array Nat := #[0]
  for h in [0:256] do
    if h < q.size then
      let x := q[h]!
      let wx := (W[x]!).getD []
      for k in [0:3] do
        let z := tm T (pickY glqGens k) x
        if z < 256 && (W[z]!).isNone then
          W := W.set! z (some (k :: wx))
          q := q.push z
  return W.map (·.getD [])

@[expose] def fmapY (T : Array (Array Nat)) (W : Array (List Nat)) (y : Nat × Nat × Nat) :
    Array Nat :=
  Array.ofFn (n := 256) fun x => evalY T y W[x.val]!

@[expose] def isHomT (T : Array (Array Nat)) (f : Array Nat) : Bool :=
  allIn 0 256 (fun x => decide (f[x]! < 256)) && allIn 1 256 (fun x => f[x]! != 0) &&
    allIn 0 256 (fun a => allIn 0 256 fun b => f[tm T a b]! == tm T f[a]! f[b]!)

@[expose] def isInvoT (f : Array Nat) : Bool := allIn 0 256 fun x => f[f[x]!]! == x

@[expose] def sigT (T : Array (Array Nat)) (x : Nat) : Bool × Bool :=
  (tpow T x 2 == 0, tpow T x 4 == 0)

@[expose] def glqTests : List (List Nat) :=
  [[0], [1], [2], [0, 1], [0, 2], [1, 2], [1, 0], [2, 0], [2, 1], [0, 1, 2]]

@[expose] def glqLevel (T : Array (Array Nat)) (k : Nat) : List Nat :=
  (List.range 256).filter fun x => x != 0 && sigT T x == sigT T (pickY glqGens k)

@[expose] def prodL {α β : Type} (l₁ : List α) (l₂ : List β) : List (α × β) :=
  l₁.flatMap fun a => l₂.map fun b => (a, b)

@[expose] def glqCands (T : Array (Array Nat)) : List (Nat × Nat × Nat) :=
  (prodL (glqLevel T 0) (prodL (glqLevel T 1) (glqLevel T 2))).filter fun y =>
    glqTests.all fun w => sigT T (evalY T y w) == sigT T (evalY T glqGens w)

@[expose] def glqAuts (T : Array (Array Nat)) (W : Array (List Nat)) : List (Nat × Nat × Nat) :=
  (glqCands T).filter fun y => isHomT T (fmapY T W y)

@[expose] def glqPairs (T : Array (Array Nat)) : List (Nat × Nat) :=
  let I := (List.range 256).filter (isInv T)
  (prodL I I).filter fun p => decide (p.1 < p.2) && tm T p.1 p.2 == tm T p.2 p.1

@[noinline, expose] def glqChecks (T : Array (Array Nat)) (W : Array (List Nat))
    (A : List (Nat × Nat × Nat)) (P : List (Nat × Nat)) : Bool :=
  W.size == 256 && allIn 0 256 (fun x => W[x]!.all (· < 3)) &&
    allIn 0 256 (fun x => evalY T glqGens W[x]! == x) &&
    W[1]! == [0] && W[3]! == [1] && W[5]! == [2] &&
    A.length == 512 && (A.filter fun y => isInvoT (fmapY T W y)).length == 176 &&
    P.all (fun p => isInv T p.1 && isInv T p.2 && p.1 != p.2 && tm T p.1 p.2 == tm T p.2 p.1) &&
    A.all fun y => let f := fmapY T W y
      !isInvoT f || P.any fun p => f[p.1]! == p.1 && f[p.2]! == p.2

@[noinline, expose] def glqWithWords (T : Array (Array Nat)) (W : Array (List Nat)) : Bool :=
  glqChecks T W (glqAuts T W) (glqPairs T)

@[noinline, expose] def glqWithTable (T : Array (Array Nat)) : Bool :=
  glqWithWords T (glqWords T)

@[noinline, expose] def glqWithEnum (S : Array Mat × Array Nat × Array Nat × Array (Array Nat)) :
    Bool :=
  glqWithTable (mulTabOf 256 S.2.1 S.2.2.1 S.2.2.2)

@[noinline, expose] def glqWithGens (us : Array Mat) : Bool := glqWithEnum (sylowBFS us 256)

@[expose] def glqCertificate (_ : Unit) : Bool :=
  glqWithGens (sylowGens (cStarArr (powM 5 111 matB 4)))

end CFSG.Sporadic.LySchreier.Native

module

public import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public import CFSG.Sporadic.Schreier.Co1ChainCheck

public section

namespace CFSG.Sporadic.Co1Block.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.ONSchreier.Native

abbrev nTri : Nat := 1365

@[expose] def triVecs (T : List (Nat × Nat)) : List Nat :=
  T.flatMap fun p => [p.1, p.2, p.1 ^^^ p.2]

@[expose] def trisOK (T : List (Nat × Nat)) (R : Rows) : Bool :=
  T.length == 1365 &&
    (triVecs T).all (fun x => decide (x < 2 ^ 24) && x != 0 && act R x == x) &&
    vSorted ((triVecs T).mergeSort fun a b => decide (a ≤ b))

@[expose] def triTable (T : List (Nat × Nat)) : Array Nat := Id.run do
  let mut tab : Array Nat := Array.replicate (2 ^ 24) 1365
  for p in T.zipIdx do
    tab := ((tab.set! p.1.1 p.2).set! p.1.2 p.2).set! (p.1.1 ^^^ p.1.2) p.2
  return tab

@[expose] def triPerm (tab : Array Nat) (T : List (Nat × Nat)) (M : Rows) : Array Nat :=
  (T.map fun p => tab[act M p.1]!).toArray

@[expose] def triOK (tab : Array Nat) (T : List (Nat × Nat)) (M : Rows) : Bool :=
  T.all fun p =>
    let k := tab[act M p.1]!
    decide (k < 1365) && tab[act M p.2]! == k && tab[act M (p.1 ^^^ p.2)]! == k

@[expose] def tableOK (tab : Array Nat) (T : List (Nat × Nat)) : Bool :=
  T.zipIdx.all fun p =>
    tab[p.1.1]! == p.2 && tab[p.1.2]! == p.2 && tab[p.1.1 ^^^ p.1.2]! == p.2

@[expose] def extendTri (X Y : Array Nat) (W : List (List Int)) : Array (Array Nat) :=
  CFSG.Sporadic.Co2Schreier.extendArrsN 1365 #[X, Y] W

@[expose] def powTri (n : Nat) (t : Array Nat) : Nat → Array Nat
  | 0 => idA n
  | k + 1 => compA n (powTri n t k) t

@[expose] def isPrimeOrderA (n : Nat) (t : Array Nat) (p : Nat) : Bool :=
  eqA n (powTri n t p) (idA n) && !(eqA n t (idA n))

@[expose] def ufFind (par : Array Nat) : Nat → Nat → Nat
  | 0, x => x
  | f + 1, x => if par[x]! == x then x else ufFind par f par[x]!

@[expose] def mergeSearchStep (n : Nat) (G : Array (Array Nat))
    (st : Array Nat × Array Nat × Array (Nat × Nat) × Array (Nat × Nat × Nat)) (h : Nat) :
    Array Nat × Array Nat × Array (Nat × Nat) × Array (Nat × Nat × Nat) := Id.run do
  let mut par := st.1
  let mut sz := st.2.1
  let mut queue := st.2.2.1
  let mut out := st.2.2.2
  if h < queue.size then
    let (u, v) := queue[h]!
    for i in [0:G.size] do
      let a := (G[i]!)[u]!
      let c := (G[i]!)[v]!
      let ra := ufFind par n a
      let rc := ufFind par n c
      if ra != rc then
        if sz[ra]! < sz[rc]! then
          par := par.set! ra rc
          sz := sz.set! rc (sz[ra]! + sz[rc]!)
        else
          par := par.set! rc ra
          sz := sz.set! ra (sz[ra]! + sz[rc]!)
        out := out.push (i, u, v)
        queue := queue.push (a, c)
  return (par, sz, queue, out)

@[expose] def mergeSearch (n : Nat) (G : Array (Array Nat)) (b x : Nat) :
    List (Nat × Nat × Nat) :=
  let par0 := (Array.ofFn (n := n) fun i => i.val).set! x b
  let sz0 := (Array.replicate n 1).set! b 2
  let st := (List.range (n + 1)).foldl (mergeSearchStep n G) (par0, sz0, #[(b, x)], #[])
  st.2.2.2.toList

end CFSG.Sporadic.Co1Block.Native

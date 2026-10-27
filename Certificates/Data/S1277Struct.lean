module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import Certificates.Data.S1277Bfs

public section

namespace Certificates.Data.S1277Struct

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Bfs Std

structure KTab where
  nb : Nat
  G0 : List B6
  appA : Array Nat
  compA : Array Nat
  invA : Array Nat
  idB : Nat

@[expose] def stabL (Γ : List B6) (c₀ : Nat) : List B6 := Γ.filter fun B => B.app c₀ == c₀

@[expose] def invIdx (G0 : List B6) (B : B6) : Nat := G0.idxOf (B.pow 59)

@[expose] def mkTab (G0 : List B6) : KTab where
  nb := G0.length
  G0 := G0
  appA := ((List.range (G0.length * 64)).map fun n => (G0.getD (n / 64) B6.id).app (n % 64)).toArray
  compA := ((List.range (G0.length * G0.length)).map fun n =>
    G0.idxOf ((G0.getD (n / G0.length) B6.id).comp (G0.getD (n % G0.length) B6.id))).toArray
  invA := (G0.map fun B => invIdx G0 B).toArray
  idB := G0.idxOf B6.id

@[expose] def mulN (T : KTab) (x y : Nat) : Nat :=
  T.compA.getD ((x / 64) * T.nb + y / 64) 0 * 64 +
    ((x % 64) ^^^ T.appA.getD ((x / 64) * 64 + y % 64) 0)

@[expose] def invN (T : KTab) (x : Nat) : Nat :=
  T.invA.getD (x / 64) 0 * 64 + T.appA.getD (T.invA.getD (x / 64) 0 * 64 + x % 64) 0

@[expose] def oneN (T : KTab) : Nat := T.idB * 64

@[expose] def klist (T : KTab) : List Nat := List.range (T.nb * 64)

@[expose] def isTwoN (T : KTab) (x : Nat) : Bool :=
  (List.range 10).foldl (fun y _ => mulN T y y) x == oneN T

@[expose] def mulMoves (T : KTab) (gens : List Nat) : List (Nat → Nat) :=
  gens.map fun g y => mulN T y g

@[expose] def conjMoves (T : KTab) (kgens : List Nat) : List (Nat → Nat) :=
  kgens.map fun g => let gi := invN T g; fun y => mulN T (mulN T g y) gi

@[expose] def mulCl (T : KTab) (gens : List Nat) : HashSet Nat :=
  bfs (mulMoves T gens) (oneN T :: gens) 1000000

structure Node where
  gens : List Nat
  elems : List Nat
deriving DecidableEq

@[expose] def sortSet (S : HashSet Nat) : List Nat := S.toList.mergeSort

@[expose] def normClosure (T : KTab) (kgens gens0 : List Nat) : Option Node :=
  let A := sortSet (bfs (conjMoves T kgens) gens0 1000000)
  let st := A.foldl (fun (st : List Nat × HashSet Nat) a =>
    if st.2.contains a then st else (st.1 ++ [a], mulCl T (st.1 ++ [a]))) ([], mulCl T [])
  if A.all st.2.contains then some ⟨st.1, sortSet st.2⟩ else none


@[expose] def bGens (T : KTab) : List Nat :=
  ((List.range T.nb).foldl (fun (st : List Nat × HashSet Nat) i =>
    if st.2.contains (i * 64) then st else (st.1 ++ [i * 64], mulCl T (st.1 ++ [i * 64])))
    ([], mulCl T [])).1

@[expose] def kgensOf (T : KTab) : List Nat :=
  [1, 2, 4, 8, 16, 32].map (fun c => T.idB * 64 + c) ++ bGens T

@[expose] def twoElems (T : KTab) : List Nat := (klist T).filter (isTwoN T)

@[expose] def cheapBad (T : KTab) (kgens : List Nat) (x : Nat) : Bool :=
  kgens.any fun g => !isTwoN T (mulN T x (mulN T (mulN T g x) (invN T g)))

@[expose] def poolElems (T : KTab) (kgens : List Nat) : List Nat :=
  (twoElems T).filter fun x => !cheapBad T kgens x

@[expose] def pcList (T : KTab) (kgens : List Nat) : List (Nat × Node) :=
  (poolElems T kgens).filterMap fun x => (normClosure T kgens [x]).bind fun N =>
    if N.elems.all (isTwoN T) then some (x, N) else none

@[expose] def distinctNodes (l : List Node) : List Node :=
  (l.foldl (fun (st : List Node × HashSet (List Nat)) N =>
    if st.2.contains N.elems then st else (N :: st.1, st.2.insert N.elems)) ([], ∅)).1.reverse

@[expose] def subsetL (a b : List Nat) : Bool :=
  let S : HashSet Nat := b.foldl (fun s x => s.insert x) ∅
  a.all S.contains


@[expose] def botNode (T : KTab) : Node := ⟨[], [oneN T]⟩

@[expose] def nodeValid (T : KTab) (N : Node) : Bool :=
  N.elems == sortSet (mulCl T N.gens) && subsetL N.gens N.elems

@[expose] def closedB (T : KTab) (kgens : List Nat) (N : Node) : Bool :=
  let S : HashSet Nat := N.elems.foldl (fun s x => s.insert x) ∅
  S.contains (oneN T) &&
    N.elems.all (fun x => N.elems.all fun y => S.contains (mulN T x y)) &&
    N.elems.all fun x => kgens.all fun g => S.contains (mulN T (mulN T g x) (invN T g))

@[expose] def joinNode (T : KTab) (kgens : List Nat) (N P : Node) : Option Node :=
  normClosure T kgens (N.gens ++ P.gens)

@[expose] def latticeRound (T : KTab) (kgens : List Nat) (PCs : List Node) (nodes : List Node) :
    List Node :=
  let known : HashSet (List Nat) := nodes.foldl (fun s N => s.insert N.elems) ∅
  let new := nodes.flatMap fun N => PCs.filterMap fun P =>
    if subsetL P.elems N.elems then none else
      (joinNode T kgens N P).bind fun J =>
        if J.elems.all (isTwoN T) && !known.contains J.elems then some J else none
  nodes ++ distinctNodes new

@[expose] def latticeNodes (T : KTab) (kgens : List Nat) (PCs : List Node) : Nat → List Node
  | 0 => [botNode T]
  | n + 1 =>
    let l := latticeNodes T kgens PCs n
    let l' := latticeRound T kgens PCs l
    if l'.length == l.length then l else l'

@[expose] def latticeOK (T : KTab) (kgens : List Nat) (PCs nodes : List Node) : Bool :=
  nodes.any (· == botNode T) &&
  nodes.all (fun N => nodeValid T N && closedB T kgens N) &&
  PCs.all (nodeValid T) &&
  nodes.all fun N => PCs.all fun P =>
    subsetL P.elems N.elems ||
      match joinNode T kgens N P with
      | some J => !J.elems.all (isTwoN T) || nodes.any (·.elems == J.elems)
      | none => false

@[expose] def pcOK (T : KTab) (kgens : List Nat) (PCs : List Node) : Bool :=
  (poolElems T kgens).all fun x =>
    match normClosure T kgens [x] with
    | some N => !N.elems.all (isTwoN T) || PCs.any (·.elems == N.elems)
    | none => false

end Certificates.Data.S1277Struct

end

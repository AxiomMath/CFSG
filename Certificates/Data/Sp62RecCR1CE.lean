module

public import Certificates.Data.Sp62RecCR1
public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def e0Words : List (List ℕ) := [[2, 10, 2, 10, 2, 10, 2, 10], [8, 11, 8, 11, 0, 2, 0, 2]]

@[expose] def gE (_ : Unit := ()) : Array (Array ℕ) := wordsA (genA ()) e0Words

@[expose] def enumE (_ : Unit := ()) : Enum := bfsEnum (gE ()) 11520

@[expose] def v0Idx : List ℕ := [0, 1, 3, 4, 5]

@[expose] def gV0 (_ : Unit := ()) : Array (Array ℕ) :=
  let G := genA ()
  Array.ofFn (n := 5) fun i => G[v0Idx.getD i.val 0]!

@[expose] def enumV0 (_ : Unit := ()) : Enum := bfsEnum (gV0 ()) 32

@[expose] def ceEnumCheck (_ : Unit := ()) : Bool :=
  let EE := enumE ()
  let EV := enumV0 ()
  enumOK EE (gE ()) && decide (EE.elems.size = 11520) && enumOK EV (gV0 ()) &&
    decide (EV.elems.size = 32) && wordsIn idxHhat e0Words

@[expose] def v0Check (_ : Unit := ()) : Bool :=
  let G := genA ()
  let EE := enumE ()
  let EV := enumV0 ()
  let L := EV.elems
  let gs := gV0 ()
  let one := idA ()
  (allLt gs.size fun j => (EE.lookup gs[j]!).isSome) &&
    (allLt L.size fun i => decide (compA L[i]! L[i]! = one)) &&
    idxHhat.all fun s => allLt gs.size fun j =>
      (EV.lookup (compA (compA G[s]! gs[j]!) G[s]!)).isSome

@[expose] def centE0Check (_ : Unit := ()) : Bool :=
  let L := (enumH ()).elems
  let gs := gE ()
  let one := idA ()
  let a := (genA ())[5]!
  allLt L.size fun i => !(commOK gs L[i]!) || decide (L[i]! = one) || decide (L[i]! = a)

@[expose] def e64Cands (L : Array (Array ℕ)) (b : Array ℕ) : List (Array ℕ) :=
  let one := idA ()
  ((List.range L.size).map fun k => L[k]!).filter fun x =>
    decide (compA x x = one) && decide (compA x b = compA b x)

@[expose] def e64Core (L : Array (Array ℕ)) (b : Array ℕ) : List (Array ℕ) :=
  let T := e64Cands L b
  T.filter fun x => decide (64 ≤ (T.filter fun y => decide (compA x y = compA y x)).length)

@[expose] def e64Check (_ : Unit := ()) : Bool :=
  let L := (enumS0 ()).elems
  let EA := enumA0 ()
  let one := idA ()
  allLt L.size fun i => (EA.lookup L[i]!).isSome || !(decide (compA L[i]! L[i]! = one)) ||
    decide ((e64Core L L[i]!).length < 64)

@[expose] def buildHomTable {Q : Type} [Monoid Q] [Inhabited Q] (E : Enum) (hs : Array Q) :
    Array Q := Id.run do
  let mut F : Array Q := #[1]
  for i in [1:E.elems.size] do
    F := F.push (F[E.parent[i]!]! * hs[E.gen[i]!]!)
  return F

@[expose] def homOK {Q : Type} [Monoid Q] [DecidableEq Q] [Inhabited Q] (E : Enum)
    (gs : Array (Array ℕ)) (hs F : Array Q) : Bool :=
  decide (F.size = E.elems.size) && decide (F[0]! = 1) &&
    allLt E.elems.size fun i => allLt gs.size fun j =>
      match E.lookup (compA E.elems[i]! gs[j]!) with
      | some k => decide (F[k]! = F[i]! * hs[j]!)
      | none => false

@[expose] def a6Sigma1 : Equiv.Perm (Fin 6) :=
  ⟨![5, 3, 1, 2, 0, 4], ![4, 2, 3, 1, 5, 0], by decide, by decide⟩

@[expose] def a6Sigma2 : Equiv.Perm (Fin 6) :=
  ⟨![5, 1, 2, 0, 4, 3], ![3, 1, 2, 5, 4, 0], by decide, by decide⟩

@[expose] def a6Imgs : Array (Equiv.Perm (Fin 6)) := #[a6Sigma1, a6Sigma2]

@[expose] def a6Table (_ : Unit := ()) : Array (Equiv.Perm (Fin 6)) :=
  buildHomTable (enumE ()) a6Imgs

@[expose] def a6Check (_ : Unit := ()) : Bool :=
  let EE := enumE ()
  let EV := enumV0 ()
  let F := a6Table ()
  homOK EE (gE ()) a6Imgs F &&
    (allLt EE.elems.size fun i => decide (F[i]! = 1) == (EV.lookup EE.elems[i]!).isSome) &&
    decide (Equiv.Perm.sign a6Sigma1 = 1) && decide (Equiv.Perm.sign a6Sigma2 = 1)

@[expose] def commV1 : List ℕ := [4]

@[expose] def commFixers : List (List ℕ) := [[2, 6], [2, 7]]

@[expose] def commConjs : List (List ℕ) :=
  [[], [2, 10], [11, 10], [2, 8, 11, 10], [2, 10, 11, 10]]

@[expose] def commExpr : List (List ℕ) := [[2, 4], [2], [0, 1], [0], [1, 2, 3]]

@[expose] def commTriple : List (List ℕ) := [[2, 10], [], [6, 10]]

@[expose] def commGWords : List (List ℕ) := commConjs.map fun c => conjWord c commV1

@[expose] def commGk (_ : Unit := ()) : Array (Array ℕ) := wordsA (genA ()) commGWords

@[expose] def commMemCheck (_ : Unit := ()) : Bool :=
  let G := genA ()
  let EE := enumE ()
  let EV := enumV0 ()
  let gk := commGk ()
  wordsIn idxHhat (commV1 :: commFixers ++ commConjs ++ commTriple) &&
    ((commFixers ++ commConjs ++ commTriple).all fun w => (EE.lookup (wordA G w)).isSome) &&
    allLt gk.size fun k => (EV.lookup gk[k]!).isSome

@[expose] def fixedBy (ds : List (Array ℕ)) (u : Array ℕ) : Bool :=
  ds.all fun d => decide (compA d u = compA u d)

@[expose] def commFixCheck (_ : Unit := ()) : Bool :=
  let G := genA ()
  let one := idA ()
  let L := (enumV0 ()).elems
  let v := wordA G commV1
  let a := G[5]!
  let ds := commFixers.map (wordA G)
  fixedBy ds v && allLt L.size fun i => !(fixedBy ds L[i]!) ||
    (decide (L[i]! = one) || decide (L[i]! = v) || decide (L[i]! = a) ||
      decide (L[i]! = compA v a))

@[expose] def commTripleCheck (_ : Unit := ()) : Bool :=
  let G := genA ()
  let one := idA ()
  let v := wordA G commV1
  let x := wordA G (conjWord (commTriple.getD 0 []) commV1)
  let y := wordA G (conjWord (commTriple.getD 1 []) commV1)
  let z := wordA G (conjWord (commTriple.getD 2 []) commV1)
  !(decide (v = one)) && !(decide (G[5]! = one)) && !(decide (x = v)) && decide (compA x y = z)

@[expose] def commExprCheck (_ : Unit := ()) : Bool :=
  let G := genA ()
  let gk := commGk ()
  (List.range 5).all fun i => ((commExpr.getD i []).all fun k => decide (k < 5)) &&
    decide (wordA gk (commExpr.getD i []) = G[v0Idx.getD i 0]!)

@[expose] def commCheck (_ : Unit := ()) : Bool :=
  commMemCheck () && commFixCheck () && commTripleCheck () && commExprCheck ()

end CFSG.ClassicalInvolution.Sp62Rec

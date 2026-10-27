module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.YGroups.ModelNative

open CFSG.Monster.B.Co2.Native

@[expose] def textLines (s : String) : List String := (s.splitOn "\n").filter fun l => !l.isEmpty

@[expose] def parseNats (line : String) : Array Nat :=
  (line.splitOn " ").foldl (fun a t => if t.isEmpty then a else a.push t.toNat!) #[]

@[expose] def parseInts (line : String) : List Int :=
  (line.splitOn " ").filterMap fun t => if t.isEmpty then none else some t.toInt!

@[expose] def parsePerms (s : String) : Array (Array Nat) :=
  ((textLines s).map parseNats).toArray

@[expose] def chainBase (s : String) : Array Nat := parseNats ((textLines s).headD "")

@[expose] def chainWords (s : String) : Array (List Int) :=
  (((textLines s).drop 1).map parseInts).toArray

@[expose] def withSign (O : Array (Array Nat)) : Array (Array Nat) :=
  O.map fun a => (a.push (a.size + 1)).push a.size

@[expose] def letterOf (n : Nat) (O : Array (Array Nat)) (c : Nat) : Array Nat :=
  if c < O.size then O[c]! else idA n

@[expose] def evalW (n : Nat) (O : Array (Array Nat)) : List Nat → Array Nat
  | [] => idA n
  | c :: w => compA n (letterOf n O c) (evalW n O w)

@[expose] def permsOK (n : Nat) (O : Array (Array Nat)) : Bool :=
  allLt O.size fun c => isInvA n O[c]! (invCand n O[c]!)

@[expose] def relatorsOK (n : Nat) (O : Array (Array Nat)) (rels : List (List Nat)) : Bool :=
  rels.all fun w => eqA n (evalW n O w) (idA n)

@[expose] def strongOf (n : Nat) (O : Array (Array Nat)) (W : Array (List Int)) :
    Array (Array Nat) × Array (Array Nat) :=
  W.foldl (init := (O, O.map (invCand n))) fun p w =>
    let t := wordA n p.1 p.2 w
    (p.1.push t, p.2.push (invCand n t))

@[expose] def levelGens (S : Array (Array Nat)) (base : Array Nat) (i : Nat) : Array (Array Nat) :=
  S.filter fun t => fixesFirst base t i

structure Orbit where
  pts : Array Nat
  pos : Array Nat
  par : Array Nat
  lab : Array Nat
deriving Inhabited

@[expose] def orbitSearch (n root : Nat) (steps : Array (Array Nat)) : Orbit := Id.run do
  let mut pos : Array Nat := (Array.replicate n n).set! root 0
  let mut pts : Array Nat := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:n] do
    if h < pts.size then
      let x := pts[h]!
      for j in [0:steps.size] do
        let y := (steps[j]!)[x]!
        if pos[y]! == n then
          pos := pos.set! y pts.size
          pts := pts.push y
          par := par.push h
          lab := lab.push j
    else
      break
  return ⟨pts, pos, par, lab⟩

@[expose] def orbitOK (n root : Nat) (steps : Array (Array Nat)) (T : Orbit) : Bool :=
  let m := T.pts.size
  decide (0 < m) && T.pts[0]! == root &&
    allLt m (fun k => decide (T.pts[k]! < n) && T.pos[T.pts[k]!]! == k) &&
    allLt m (fun k => k == 0 || (decide (T.par[k]! < k) && decide (T.lab[k]! < steps.size) &&
      (steps[T.lab[k]!]!)[T.pts[T.par[k]!]!]! == T.pts[k]!))

@[expose] def chainOK (n : Nat) (O : Array (Array Nat)) (W : Array (List Int))
    (base : Array Nat) : Bool :=
  let p := strongOf n O W
  let S := p.1
  let Sinv := p.2
  permsOK n O && decide (S.size = O.size + W.size) && decide (Sinv.size = S.size) &&
    allLt O.size (fun k => eqA n S[k]! O[k]!) &&
    allLt S.size (fun j => isInvA n S[j]! Sinv[j]!) &&
    allLt W.size (fun i => lettersOK (O.size + i) W[i]! &&
      eqA n S[O.size + i]! (wordA n S Sinv W[i]!)) &&
    allLt base.size (fun i => decide (base[i]! < n)) &&
    allLt base.size (fun i => orbitOK n base[i]! (levelGens S base i)
      (orbitSearch n base[i]! (levelGens S base i)))

@[expose] def chainSizes (n : Nat) (O : Array (Array Nat)) (W : Array (List Int))
    (base : Array Nat) : List Nat :=
  let S := (strongOf n O W).1
  (List.range base.size).map fun i => (orbitSearch n base[i]! (levelGens S base i)).pts.size

end CFSG.YGroups.ModelNative

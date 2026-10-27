module

public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import Std.Data.HashMap

public section

namespace Certificates.Thm49E

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native

abbrev E : Type := Bool × Array ℕ

@[expose] def idE (_ : Unit := ()) : E := (false, idA 1755)

@[expose] def mulE (a b : E) : E := (xor a.1 b.1, compA 1755 a.2 b.2)

@[expose] def invE (a : E) : E := (a.1, invCand 1755 a.2)

@[expose] def eqE (a b : E) : Bool := a.1 == b.1 && eqA 1755 a.2 b.2

@[expose] def tauE (_ : Unit := ()) : E := (true, idA 1755)

@[expose] def inAE (p : Array ℕ) : E := (false, p)

@[expose] def evalWordE (a : Array E) (w : List ℕ) : E :=
  w.foldr (fun l acc => mulE a[l]! acc) (idE ())

@[expose] def lookupE (L : Array E) (x : E) : Option ℕ := L.findIdx? fun y => eqE y x

@[expose] def aWord (w : List ℤ) : Array ℕ := wordArr 1755 titsGenArrs w

@[expose] def zArr (_ : Unit := ()) : Array ℕ := titsZArr

structure Orb (α : Type) where
  ls : Array α
  par : Array ℕ
  gen : Array ℕ

@[expose] partial def orbBFS {α : Type} [BEq α] [Hashable α] [Inhabited α] (ngen : ℕ)
    (act : ℕ → α → α) (x0 : α) : Orb α := Id.run do
  let mut ls : Array α := #[x0]
  let mut par : Array ℕ := #[0]
  let mut gen : Array ℕ := #[0]
  let mut seen : Std.HashMap α Unit := (Std.HashMap.emptyWithCapacity 4096).insert x0 ()
  let mut q := 0
  while q < ls.size do
    let x := ls[q]!
    for g in [0:ngen] do
      let y := act g x
      if !seen.contains y then
        seen := seen.insert y ()
        ls := ls.push y
        par := par.push q
        gen := gen.push g
    q := q + 1
  return ⟨ls, par, gen⟩

@[expose] def conjArr (s si x : Array ℕ) : Array ℕ := compA 1755 (compA 1755 s x) si

@[expose] def dGen (_ : Unit := ()) : Array (Array ℕ) :=
  #[titsDArr 0, titsDArr 1, invCand 1755 (titsDArr 0), invCand 1755 (titsDArr 1)]

@[expose] def dGenInv (_ : Unit := ()) : Array (Array ℕ) :=
  #[invCand 1755 (titsDArr 0), invCand 1755 (titsDArr 1), titsDArr 0, titsDArr 1]

@[expose] def lOrb (_ : Unit := ()) : Orb (Array ℕ) :=
  let S := dGen ()
  let Si := dGenInv ()
  orbBFS 4 (fun g x => conjArr S[g]! Si[g]! x) (zArr ())

@[expose] def orbDerivOK (ngen : ℕ) (act : ℕ → Array ℕ → Array ℕ) (x0 : Array ℕ)
    (o : Orb (Array ℕ)) : Bool :=
  o.par.size == o.ls.size && o.gen.size == o.ls.size && decide (0 < o.ls.size) &&
    eqA 1755 o.ls[0]! x0 &&
    allLt o.ls.size fun i => decide (i = 0) ||
      (decide (o.par[i]! < i) && decide (o.gen[i]! < ngen) &&
        eqA 1755 o.ls[i]! (act o.gen[i]! o.ls[o.par[i]!]!))

@[expose] def orbClosedOK (ngen : ℕ) (act : ℕ → Array ℕ → Array ℕ) (o : Orb (Array ℕ)) : Bool :=
  allLt o.ls.size fun i => allLt ngen fun g =>
    let z := act g o.ls[i]!
    o.ls.any fun y => eqA 1755 y z

@[expose] def distinctOK (ls : Array (Array ℕ)) : Bool :=
  allLt ls.size fun i => allLt i fun j => !eqA 1755 ls[i]! ls[j]!

@[expose] def commArr1755 (x y : Array ℕ) : Bool := eqA 1755 (compA 1755 x y) (compA 1755 y x)

@[expose] def memArr (ls : Array (Array ℕ)) (x : Array ℕ) : Bool := ls.any fun y => eqA 1755 y x

@[expose] def zpWord : List ℤ := [-2, -2]

@[expose] def y0Word : List ℤ := [-2, -2, -2, -4, 3, 2, 4, 1, 4, 3, 4, -3, -4, -3]

@[expose] def u1Word : List ℤ := [-4, 2, 1, 4, 1, -2, 4, 1, -2]

@[expose] def u2Word : List ℤ := [-2, -4, -2, 3, 4, 3, 2, 3, 4, 3]

@[expose] def l2Word : List ℤ := [-2, -4, 2, 1, -2, 3, 2, 2, 3, 4, -1, -2]

@[expose] def l3Word : List ℤ := [-4]

@[expose] def h1Word : List ℤ := [3, 4, 3, 2, 3, 4, 3]

@[expose] def h2Word : List ℤ := [2]

@[expose] def zpArr (_ : Unit := ()) : Array ℕ := aWord zpWord

@[expose] def y0Arr (_ : Unit := ()) : Array ℕ := aWord y0Word

end Certificates.Thm49E

module

public import Certificates.Data.YamakiEnum

public section

namespace CFSG.CGT.Foote82.InvolA6

open CFSG.ClassicalInvolution.Solomon73.Yamaki

@[inline, expose] def anyLt (n : ℕ) (p : ℕ → Bool) : Bool := Nat.any n fun i _ => p i

@[expose] def permArr (p : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 64) fun i => if i.val < 6 then p[i.val]! else i.val

@[expose] def genX (_ : Unit := ()) : Array ℕ := permArr #[1, 0, 3, 2, 4, 5]

@[expose] def genY (_ : Unit := ()) : Array ℕ := permArr #[1, 2, 4, 5, 0, 3]

@[expose] def a6Gens (_ : Unit := ()) : Array (Array ℕ) := #[genX (), genY ()]

@[expose] def a6Enum (_ : Unit := ()) : Enum := bfsEnum (a6Gens ()) 360

@[expose] def invArr (t : Array ℕ) : Array ℕ :=
  (List.range 64).foldl (fun r j => r.set! t[j]! j) (Array.replicate 64 0)

@[expose] def invTab (E : Enum) : Array ℕ :=
  E.elems.map fun t => (E.lookup (invArr t)).getD 0

@[expose] def invOK (E : Enum) (inv : Array ℕ) : Bool :=
  let one := idA ()
  allLt E.elems.size fun i =>
    decide (inv[i]! < E.elems.size) && compA E.elems[i]! E.elems[inv[i]!]! == one

@[expose] def pow5 (w : Array ℕ) : Array ℕ := compA w (compA w (compA w (compA w w)))

@[expose] def pathVal (E : Enum) (hs : Array (Array ℕ)) (one : Array ℕ) : ℕ → ℕ → Array ℕ
  | 0, _ => one
  | fuel + 1, i =>
    if i = 0 then one else compA (pathVal E hs one fuel E.parent[i]!) hs[E.gen[i]!]!

@[expose] def caseA (E : Enum) (inv : Array ℕ) (one : Array ℕ) (F : Array (Array ℕ)) : Bool :=
  anyLt E.elems.size fun i =>
    let w := compA F[i]! E.elems[inv[i]!]!
    let w2 := compA w w
    !(w2 == one) && compA w2 w2 == one

@[expose] def caseB (E : Enum) (inv : Array ℕ) (cand : List ℕ) (one : Array ℕ)
    (F : Array (Array ℕ)) : Bool :=
  (cand.any fun ia => cand.any fun ib =>
    let a := E.elems[ia]!
    let b := E.elems[ib]!
    ((F[ia]! == E.elems[inv[ia]!]! && F[ib]! == b) || (F[ia]! == b && F[ib]! == a)) &&
      decide (ia < E.elems.size) && decide (ib < E.elems.size) &&
      compA (compA a a) a == one && compA (compA b b) b == one && !(a == one) &&
      compA a b == compA b a && !(b == one) && !(b == a) && !(b == compA a a)) &&
  anyLt E.elems.size fun ig =>
    let w := compA F[ig]! E.elems[inv[ig]!]!
    !(w == one) && compA w w == one

@[expose] def pairOK (E : Enum) (inv : Array ℕ) (cand : List ℕ) (one X Y : Array ℕ)
    (iu iv : ℕ) : Bool :=
  let u := E.elems[iu]!
  let v := E.elems[iv]!
  !(pow5 (compA u v) == one) || !(pow5 (compA u (compA v v)) == one) || (u == X && v == Y) ||
    !(pathVal E #[u, v] one E.elems.size iu == X && pathVal E #[u, v] one E.elems.size iv == Y) ||
    (let F := buildF E #[u, v]
     caseA E inv one F || caseB E inv cand one F)

@[expose] def autCheckWith (E : Enum) (inv : Array ℕ) (X Y : Array ℕ) : Bool :=
  let one := idA ()
  let n := E.elems.size
  let L2 := (List.range n).filter fun i => compA E.elems[i]! E.elems[i]! == one
  let L4 := (List.range n).filter fun i =>
    let t2 := compA E.elems[i]! E.elems[i]!
    compA t2 t2 == one
  let cand := (List.range n).filter fun i =>
    let t := E.elems[i]!
    compA (compA t t) t == one && !(t == one)
  L2.all fun iu => L4.all fun iv => pairOK E inv cand one X Y iu iv

@[expose] def a6EnumCheck (_ : Unit := ()) : Bool :=
  let E := a6Enum ()
  enumOK E (a6Gens ()) && E.elems.size == 360

@[expose] def a6InvCheck (_ : Unit := ()) : Bool :=
  let E := a6Enum ()
  invOK E (invTab E)

@[expose] def a6AutCheck (_ : Unit := ()) : Bool :=
  let E := a6Enum ()
  autCheckWith E (invTab E) (genX ()) (genY ())

end CFSG.CGT.Foote82.InvolA6

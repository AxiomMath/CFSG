module

public import Certificates.Data.Sp62RecCR1

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def z6Pos (E : Enum) (t : Array ℕ) : ℕ := (E.lookup t).getD 0

@[expose] def z6Gl (i : ℕ) : Array ℕ :=
  let E := enumA0 ()
  let G := genA ()
  Array.ofFn (n := 64) fun k => z6Pos E (compA (compA G[i]! E.elems[k.val]!) G[i]!)

@[expose] def z6MulTab (_ : Unit := ()) : Array (Array ℕ) :=
  let E := enumA0 ()
  Array.ofFn (n := 64) fun i => Array.ofFn (n := 64) fun j =>
    z6Pos E (compA E.elems[i.val]! E.elems[j.val]!)

@[expose] def z6GsL (_ : Unit := ()) : Array (Array ℕ) := #[z6Gl 0, compA (z6Gl 9) (z6Gl 10)]

@[expose] def z6EnumL (_ : Unit := ()) : Enum := bfsEnum (z6GsL ()) 200

@[expose] def z6LbarCheck (_ : Unit := ()) : Bool :=
  let EL := z6EnumL ()
  let gs := z6GsL ()
  enumOK EL gs && decide (EL.elems.size = 168) &&
    (List.range 11).all (fun i => (EL.lookup (z6Gl i)).isSome) &&
    decide (compA gs[0]! gs[0]! = idA ()) && decide (compA gs[1]! (compA gs[1]! gs[1]!) = idA ())

@[expose] def z6Beta : ℕ := 3

@[expose] def z6J : List (List ℕ) := [[0, 5, 14], [0, 2, 3], [0], [2, 5, 8], [2], [5]]

@[expose] def z6Img (mul : Array (Array ℕ)) (T : Array (Array ℕ)) (v : ℕ) : Array ℕ :=
  (z6J.map fun J => J.foldr (fun m acc => (mul[(T[m]!)[v]!]!)[acc]!) 0).toArray

@[expose] def z6BPos (_ : Unit := ()) : Array ℕ :=
  let E := enumA0 ()
  (gA0 ()).map fun t => z6Pos E t

@[expose] def z6OrbCheck (_ : Unit := ()) : Bool :=
  let EL := z6EnumL ()
  decide (z6Img (z6MulTab ()) EL.elems z6Beta = z6BPos ()) &&
    z6J.all (fun J => J.all fun m => decide (m < 168)) && decide (z6Beta < 64)

@[expose] def z6IsPerm (F : Array ℕ) : Bool :=
  decide (F.size = 64) && allLt 64 fun i =>
    decide (F[i]! < 64) && allLt i fun j => decide (F[j]! ≠ F[i]!)

@[expose] def z6IsMul (mul : Array (Array ℕ)) (F : Array ℕ) : Bool :=
  allLt 64 fun i => allLt 64 fun j => decide (F[(mul[i]!)[j]!]! = (mul[F[i]!]!)[F[j]!]!)

@[expose] def z6IsNorm (gs tt : Array (Array ℕ)) (F : Array ℕ) : Bool :=
  allLt gs.size fun j => decide (compA F gs[j]! = compA tt[j]! F)

@[expose] def z6Valid (mul gs tt : Array (Array ℕ)) (F : Array ℕ) : Bool :=
  z6IsNorm gs tt F && z6IsPerm F && z6IsMul mul F

@[expose] def z6TEqn (EL : Enum) (tt T : Array (Array ℕ)) : Bool :=
  decide (T.size = EL.elems.size) && decide (T[0]? = some (idA ())) &&
    allLt EL.elems.size fun m => decide (m = 0) ||
      decide (T[m]! = compA T[EL.parent[m]!]! tt[EL.gen[m]!]!)

@[expose] def z6BuildF (mul : Array (Array ℕ)) (E : Enum) (img : Array ℕ) : Array ℕ :=
  Id.run do
    let mut F : Array ℕ := #[0]
    for k in [1:64] do
      F := F.push ((mul[F[E.parent[k]!]!]!)[img[E.gen[k]!]!]!)
    return F

@[expose] def z6FEqn (mul : Array (Array ℕ)) (E : Enum) (img F : Array ℕ) : Bool :=
  decide (F.size = 64) && decide (F[0]? = some 0) &&
    allLt 64 fun k => decide (k = 0) ||
      decide (F[k]! = (mul[F[E.parent[k]!]!]!)[img[E.gen[k]!]!]!)

@[expose] def z6NormCheck (_ : Unit := ()) : Bool :=
  let EL := z6EnumL ()
  let E := enumA0 ()
  let gs := z6GsL ()
  let mul := z6MulTab ()
  allLt 168 fun ia => allLt 168 fun ib =>
    let tt := #[EL.elems[ia]!, EL.elems[ib]!]
    (!decide (compA tt[0]! tt[0]! = idA ())) ||
      (!decide (compA tt[1]! (compA tt[1]! tt[1]!) = idA ())) ||
      (let T := buildF EL tt
       z6TEqn EL tt T && allLt 64 fun v =>
        let img := z6Img mul T v
        let F := z6BuildF mul E img
        z6FEqn mul E img F && (!z6Valid mul gs tt F || (EL.lookup F).isSome))

end CFSG.ClassicalInvolution.Sp62Rec

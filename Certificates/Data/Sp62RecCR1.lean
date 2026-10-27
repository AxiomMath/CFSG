module

public import Certificates.Data.YamakiTables
public import Certificates.Data.YamakiZRig

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def gA0 (_ : Unit := ()) : Array (Array ℕ) :=
  let G := genA ()
  Array.ofFn (n := 6) fun i => G[i.val + 3]!

@[expose] def enumA0 (_ : Unit := ()) : Enum := bfsEnum (gA0 ()) 64

@[expose] def a0EnumCheck (_ : Unit := ()) : Bool :=
  let E := enumA0 ()
  enumOK E (gA0 ()) && decide (E.elems.size = 64) && decide ((enumS0 ()).elems.size = 512)

@[expose] def a0AbelCheck (_ : Unit := ()) : Bool :=
  let L := (enumA0 ()).elems
  let one := idA ()
  allLt L.size fun i => decide (compA L[i]! L[i]! = one) &&
    allLt L.size fun j => decide (compA L[i]! L[j]! = compA L[j]! L[i]!)

@[expose] def hhatAlphaCheck (_ : Unit := ()) : Bool :=
  let G := genA ()
  idxHhat.all fun i => decide (compA G[i]! G[5]! = compA G[5]! G[i]!)

@[expose] def conjWord (c x : List ℕ) : List ℕ := c ++ x ++ c.reverse

@[expose] def fourOK (x c₁ c₂ : List ℕ) : Bool :=
  let G := genA ()
  let a := wordA G x
  let b := wordA G (conjWord c₁ x)
  wordsIn idxHhat [c₁, c₂] && !(decide (a = idA ())) && !(decide (b = a)) &&
    decide (compA a b = compA b a) && decide (wordA G (conjWord c₂ x) = compA a b)

@[expose] def fourCheck (_ : Unit := ()) : Bool :=
  fourOK [4] [10] [2, 10] && fourOK [5, 4] [10, 11, 10] [7, 10, 11, 10]

end CFSG.ClassicalInvolution.Sp62Rec

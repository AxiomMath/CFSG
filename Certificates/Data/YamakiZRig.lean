module

public import Certificates.Data.YamakiEnum

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def countLt (n : ℕ) (p : ℕ → Bool) : ℕ := (List.range n).countP p

@[expose] def sqCount (E : Enum) (a : Array ℕ) : ℕ :=
  countLt E.elems.size fun i => decide (compA E.elems[i]! E.elems[i]! = a)

@[expose] def commOK (gs : Array (Array ℕ)) (a : Array ℕ) : Bool :=
  allLt gs.size fun j => decide (compA a gs[j]! = compA gs[j]! a)

@[expose] def centerOK (E : Enum) (gs : Array (Array ℕ)) (a b : Array ℕ) : Bool :=
  let one := idA ()
  let c := compA a b
  allLt E.elems.size fun i =>
    !(commOK gs E.elems[i]!) || (decide (E.elems[i]! = one) || (decide (E.elems[i]! = a) ||
      (decide (E.elems[i]! = b) || decide (E.elems[i]! = c))))

@[expose] def gS0 (_ : Unit := ()) : Array (Array ℕ) :=
  let G := genA ()
  Array.ofFn (n := 9) fun i => G[i.val]!

@[expose] def enumS0 (_ : Unit := ()) : Enum := bfsEnum (gS0 ()) 512

end CFSG.ClassicalInvolution.Solomon73.Yamaki

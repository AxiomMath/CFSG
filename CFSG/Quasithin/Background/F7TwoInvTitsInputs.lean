module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def invTitsZConjWord : List ℤ := [1, -2]

@[expose] def invTitsTConjWord : List ℤ := [1, -2, -1]

@[expose] def invTitsComm (c d : Array ℕ) : Array ℕ :=
  compA 1755 (compA 1755 c d) (compA 1755 c (invCand 1755 d))

@[expose] def invTitsPow (a : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 1755
  | k + 1 => compA 1755 a (invTitsPow a k)

@[expose] def invTitsHasOrder (a : Array ℕ) (p : ℕ) : Bool :=
  eqA 1755 (invTitsPow a p) (idA 1755) && !eqA 1755 a (idA 1755)

@[expose] def invTitsClassCheck (w gw : List ℤ) (p q : ℕ) : Bool :=
  let g := wordArr 1755 titsDerivedArrs gw
  let r' := conjArr g (wordArr 1755 titsDerivedArrs w)
  lettersOK 13 w && lettersOK 13 gw && isInvA 1755 g (invCand 1755 g) &&
    eqA 1755 (compA 1755 r' r') (idA 1755) &&
    invTitsHasOrder (invTitsComm r' titsDerivedArrs[0]!) p &&
    invTitsHasOrder (invTitsComm r' titsDerivedArrs[1]!) q

@[expose] def invTitsCheck (_ : Unit) : Bool :=
  invTitsClassCheck titsCenterWord invTitsZConjWord 5 5 &&
    invTitsClassCheck titsTWord invTitsTConjWord 13 13

end CFSG.Quasithin.F7Two

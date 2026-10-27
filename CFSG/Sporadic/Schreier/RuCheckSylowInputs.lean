
module

public import CFSG.Sporadic.Schreier.RuCheckChainsBase
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuCheckChainsBase
public meta import CFSG.Sporadic.Schreier.RuEnum

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruSF (j : ℕ) : Array ℕ := (ruField1920 1)[j]!

@[expose] def ruRF (i : ℕ) : Array ℕ := (ruField1920 4)[i]!

@[expose] def ruZF : Array ℕ := resA ruF ruFPos ruZA

@[expose] def ruCommA (n : ℕ) (a b : Array ℕ) : Array ℕ :=
  compA n (compA n (compA n a b) (invCand n a)) (invCand n b)

@[expose] def ruCommutesS (g : Array ℕ) : Bool :=
  allLt 4 fun j => eqA 1920 (compA 1920 g (ruSF j)) (compA 1920 (ruSF j) g)

end CFSG.Sporadic.RuSchreier

module

public import CFSG.LieType.Simplicity.TitsBits

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree

@[expose] def rb (a : ℕ) : ℕ := pack (eltBits a)

@[expose] def tB : ℕ := rb 43

@[expose] def uB : ℕ := rb 44

@[expose] def tuB : ℕ := mul (rb 43) (rb 44)

@[expose] def vB : ℕ := mul (rb 36) (rb 35)

@[expose] def posPL : List ℕ := [1, 7, 15, 43]

@[expose] def posNL : List ℕ := [6, 14, 23, 46]

@[expose] def sB (i : ℕ) : ℕ := mul (rb (posPL.getD i 0)) (rb (posNL.getD i 0))

@[expose] def sqB (x : ℕ) : ℕ := mul x x

@[expose] def rAB : ℕ := sB 3

@[expose] def rBB : ℕ := mul (sB 0) (sB 1)

@[expose] def zB : ℕ := mul (mul (sqB (sB 0)) (sqB (sB 1))) (sqB (sB 2))

end CFSG.RankThree.PartTwo.Sec21.FF81.F4

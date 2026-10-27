module

public import CFSG.Certificates.Kernel.Common.XorBits

public section

namespace CFSG.KC.F2FixRank

open CFSG.KC.XorBits

@[expose] def fixRankOK (c B : ℕ → ℕ) (fs : List ℕ) (n : ℕ) : Bool :=
  (List.range n).all fun j => fs.contains j || xorB B (c j ^^^ 2 ^ j) n == 2 ^ j

end CFSG.KC.F2FixRank

end

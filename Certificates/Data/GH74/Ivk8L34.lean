module

public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public meta import Certificates.Data.GH74.Ivk8Weak
public meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace Certificates.Ivk8Weak.L34

open CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native
  CFSG.Certificates

@[expose] def wordA : List ℤ :=
  [-2, -2, -3, -2]

@[expose] def wordB : List ℤ :=
  [-3, -1, 2, 3, 3, 1, -3, -1, 2, 1]

@[expose] def rChain : RawSchreierDatum 42 :=
  certificate (by decide) [g₁, g₂, g₃, g₄, g₅, g₆]
    [[-1, 2, 1], [4, 7, 4], [-5, 4, -1, 4, 1], [-6, 2, 6]] #v[0, 1, 6, 3, 5, 2] (by decide)

end Certificates.Ivk8Weak.L34

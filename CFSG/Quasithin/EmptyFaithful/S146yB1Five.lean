module

public import CFSG.Quasithin.EmptyFaithful.S146yL3ParAut

public section

namespace CFSG.Quasithin

structure B1ResiduesFive : Prop where
  borel : BorelAutFree
  l2Prime : L2PrimeOnList115
  l2Square : L2SquareNotOnList115
  u3Odd : U3OddNotOnList115
  l3Odd : L3OddNotOnList115

theorem B1ResiduesFive.toResidues (h : B1ResiduesFive) : B1Residues :=
  ⟨h.borel, h.l2Prime, h.l2Square, h.u3Odd, h.l3Odd, l3TwoParabolicAut_proof⟩

end CFSG.Quasithin

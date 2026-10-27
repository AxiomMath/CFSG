module

public import CFSG.Quasithin.EmptyFaithful.S146yB1Five
public import CFSG.Quasithin.EmptyFaithful.S146yBorel

public section

namespace CFSG.Quasithin

structure B1ResiduesFour : Prop where
  l2Prime : L2PrimeOnList115
  l2Square : L2SquareNotOnList115
  u3Odd : U3OddNotOnList115
  l3Odd : L3OddNotOnList115

theorem B1ResiduesFour.toFive (h : B1ResiduesFour) : B1ResiduesFive :=
  ⟨borelAutFree_proof, h.l2Prime, h.l2Square, h.u3Odd, h.l3Odd⟩

end CFSG.Quasithin

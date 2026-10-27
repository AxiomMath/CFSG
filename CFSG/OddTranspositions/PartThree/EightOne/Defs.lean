module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.OddTranspDefs

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72

namespace EightOne

abbrev twoOddCore (G : Type) [Group G] [Finite G] : Subgroup G :=
  (CFSG.oddCore (G ⧸ CFSG.pCore 2 G)).comap (QuotientGroup.mk' (CFSG.pCore 2 G))

end EightOne

end CFSG.OddTranspositions.PartThree

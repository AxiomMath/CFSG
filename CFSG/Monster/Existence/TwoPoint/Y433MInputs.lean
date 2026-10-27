module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.Existence.TwoPoint.Fi23S4Data
public import CFSG.Monster.Griess.Short
public import CFSG.Sporadic.Bridge.Common
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public import Certificates.Data.CFSGNative.YGroups.Felsch

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.YGroups
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels powWord)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

@[expose] def fiCox (i j : ℕ) : ℕ :=
  if (min i j, max i j) ∈
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 9), (3, 7), (7, 8)] : List (ℕ × ℕ))
    then 3 else 2

end CFSG.Monster.Existence

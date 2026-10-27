module

public import CFSG.OddTranspositions.SevenThreeKind
public import CFSG.Timmesfeld.Bridge.Asc72Local

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem Delta_eq_centSet (z : G) : Delta D z = centSet D z :=
  Set.ext fun _ => mem_Delta_iff

theorem thirdK_eq_localGroup (z : G) : thirdK D z = localGroup D z :=
  congrArg Subgroup.closure (Delta_eq_centSet z)

end CFSG.OddTranspositions

module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.Open
open scoped MatrixGroups

@[expose] def standardOddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}

instance standardOddCore_normal (H : Type*) [Group H] : (standardOddCore H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

abbrev standardIsStandardSubgroup {G : Type*} [Group G] (L : Subgroup G) : Prop :=
  standardComponentIsStandard L

end CFSG.Open
module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.Milestones.ASVolI.I6
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

open CFSG.Quasithin CFSG.Open Subgroup CFSG.ASVolI.ChIJK
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def omegaWithin (V H E L : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ omegaSet V H E ∧ U ≤ L}

@[expose] def IsGeneratedByOmega (V H E L : Subgroup G) : Prop :=
  (⨆ U ∈ omegaWithin V H E L, U) = L

end CFSG.LocalAnalysis.WeakClosure81.SevenK

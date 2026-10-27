module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 4: Theorem (4.7)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4Scratch
universe u
universe v
open Section1 Section2 Section3 Section4

/-! ## (4.7) -/

@[expose] public def theorem_4_7_statement
    {L : Type u} [Group L] [Finite L]
    (K H : Subgroup L)
    (A : Set L) : Prop :=
  ∀ X : ClassFunction K,
    Section1.IsIrreducibleCharacterOnGroup X →
      ¬ Section1.subgroupInKernel' X (H.subgroupOf K) →
        Section1.supportedOn X (withOne (subgroupPullbackSet K A)) ∧
          Section1.supportedOn (Section1.inducedCF K X) (withOne A)

@[expose] public def theorem_4_7_nonbase_column_statement
    {L : Type u} [Group L] [Finite L]
    (K H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I]
    (j0 : J)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K) : Prop :=
  ∀ j, j ≠ j0 →
    ¬ Section1.subgroupInKernel' (xChar j) (H.subgroupOf K) ∧
      Section1.supportedOn (xChar j) (withOne (subgroupPullbackSet K A)) ∧
        Section1.supportedOn (piColumn piChar j) (withOne A)

@[expose] public def theorem_4_7_full_statement
    {L : Type u} [Group L] [Finite L]
    (K H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I]
    (j0 : J)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K) : Prop :=
  theorem_4_7_statement K H A ∧
    theorem_4_7_nonbase_column_statement K H A j0 piChar xChar

end CFSG.Section4Scratch

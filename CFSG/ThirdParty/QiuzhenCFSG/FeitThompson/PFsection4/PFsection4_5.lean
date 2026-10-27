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
# Peterfalvi, Section 4: Theorem (4.5)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4Scratch
universe u
universe v
open Section1 Section2 Section3 Section4

/-! ## (4.5) -/

@[expose] public def theorem_4_5_a_statement
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K) : Prop :=
  (∀ i j, Section1.subgroupRestriction K (piChar i j) = xChar j) ∧
    (∀ j, Section1.IsIrreducibleCharacterOnGroup (xChar j)) ∧
    ∀ j, Section1.inducedCF K (xChar j) = piColumn piChar j

@[expose] public def theorem_4_5_b_statement
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K) : Prop :=
  (∀ X : ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup X →
        X ∉ Set.range xChar →
          Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X) ∧
            Section1.inducedCF K X ∉ Set.range (fun p : I × J => piChar p.1 p.2)) ∧
    ∀ ψ : ClassFunction L,
      Section1.IsIrreducibleCharacterOnGroup ψ →
        ψ ∈ Set.range (fun p : I × J => piChar p.1 p.2) ∨
          ∃ X : ClassFunction K,
            Section1.IsIrreducibleCharacterOnGroup X ∧
              X ∉ Set.range xChar ∧
                ψ = Section1.inducedCF K X

@[expose] public def theorem_4_5_statement
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → ClassFunction L) : Prop :=
  ∃ xChar : J → ClassFunction K,
    theorem_4_5_a_statement K piChar xChar ∧
      theorem_4_5_b_statement K piChar xChar

end CFSG.Section4Scratch

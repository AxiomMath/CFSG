module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 6: Theorem (6.1)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6
universe u
universe v

@[expose] public def hypothesis_6_1_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup L)
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Section5.hypothesis_5_2_statement S T ∧
    K.Normal ∧
    IsSolvable K ∧
    inducedKernelFamily K ⊥ S

public theorem hypothesis_6_1_hypothesis_5_2
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_6_1_statement K S T) :
    Section5.hypothesis_5_2_statement S T :=
  h.1

public theorem hypothesis_6_1_inducedKernelFamily_bot
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_6_1_statement K S T) :
    inducedKernelFamily K ⊥ S :=
  h.2.2.2

end CFSG.Section6

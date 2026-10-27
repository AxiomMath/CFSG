module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 6: Theorem (6.4)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6
universe u
universe v

@[expose] public def hypothesis_6_4_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K M H1 : Subgroup L)
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_6_1_statement K S T ∧
    Odd (Nat.card L) ∧
    M ≤ H1 ∧
      M ≤ K ∧
        nilpotentQuotient M K ∧
          commutatorQuotientHypothesis M H1 K ∧
            frobeniusQuotientWithKernel K H1

end CFSG.Section6

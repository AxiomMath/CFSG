module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_8

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Lemma 1.9
**Stmt**:
Let `π` be a set of primes.
Let `G` be a finite solvable `π`-group.
Let `A` be an operator group on `G` that stablizes a normal series of `G`.
Then `A/C_A(G)` is a `π`-group.
-/

public theorem CFSG.lemma_1_9 {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (π : Set Nat.Primes) (hsolv : Group.IsSolvable G) (hpi : IsPiGroup π G)
    (hstab : ∃ (ι : Type*) (Gi : ι → Subgroup G) (next : ι → ι),
      StabilizesNormalSeries (G := G) (A := A) Gi next)
    (hker : (fixingSubgroupOf A G (Set.univ : Set G)).Normal) :
    IsPiGroup (π := π) (A ⧸ fixingSubgroupOf A G (Set.univ : Set G)) := by
  exact
    isPiGroup_quotient_fixingSubgroup_of_stabilizesNormalSeries
      (G := G) (A := A) π hsolv hpi hstab hker


end

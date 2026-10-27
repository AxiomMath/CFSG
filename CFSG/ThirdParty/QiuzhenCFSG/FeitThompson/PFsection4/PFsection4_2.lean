module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 4: Theorem (4.2)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4
universe u
universe v

/-! ## (4.2) -/

/--
Peterfalvi Hypothesis (4.2): `L = K ⋊ W₁` with `W₁` a nontrivial cyclic Hall
subgroup, there is a nontrivial cyclic subgroup `W₂ ≤ K` such that
`C_K(x) = W₂` for every nonidentity `x ∈ W₁`, and `W = W₁ × W₂` has odd
order.
-/
@[expose] public def hypothesis_4_2_statement
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) : Prop :=
  Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W1 ∧
    (∃ π : Set Nat.Primes, IsHallSubgroup π W1) ∧
    IsCyclic W1 ∧
    Nat.card W1 ≠ 1 ∧
    IsCyclic W2 ∧
    Nat.card W2 ≠ 1 ∧
    (∀ x : W1, x ≠ 1 → Section2.centralizerIn K (x : L) = W2) ∧
    W1 ≤ W ∧
    W2 ≤ W ∧
    Section2.IsInternalDirectProduct W W1 W2 ∧
    Odd (Nat.card W)


end CFSG.Section4

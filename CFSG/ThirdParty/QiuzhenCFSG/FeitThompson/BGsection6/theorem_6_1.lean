module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct

/-! # Theorem 6.1 from BG Section 6 -/

public theorem CFSG.theorem_6_1
    {G : Type*} [Group G] [Group.IsSolvable G] (ho : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (A : Subgroup S) [A.Normal] [IsMulCommutative A] :
    A.map S.toSubgroup.subtype ≤ Op_p'p p G := by
  let : Finite G := card_odd_finite ho
  exact sylow_abelian_normal_le_op_pPrime_p
    (G := G) (hsolv := inferInstance) ho S A

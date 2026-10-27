module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Relative index in a product with a normal subgroup -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If a normal subgroup `N` together with `K` generates a finite group,
then the index of `K` is the index of `N ∩ K` in `N`. -/
public theorem index_eq_relIndex_inf_of_normal_sup
    {G : Type u} [Group G] [Finite G]
    (N K : Subgroup G) (hN : N.Normal) (hNK : N ⊔ K = ⊤) :
    K.index = (N ⊓ K).relIndex N := by
  classical
  let : N.Normal := hN
  let b : G ⧸ K := QuotientGroup.mk (1 : G)
  have horbit : MulAction.orbit N b = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    have hg : g ∈ N ⊔ K := by
      rw [hNK]
      trivial
    rcases ((@Subgroup.mem_sup_of_normal_left G _ N K hN g).mp hg) with
      ⟨n, hn, k, hk, rfl⟩
    refine ⟨⟨n, hn⟩, ?_⟩
    change (n : G) • (QuotientGroup.mk (1 : G) : G ⧸ K) =
      (QuotientGroup.mk (n * k : G) : G ⧸ K)
    have hsmul : (n : G) • (QuotientGroup.mk (1 : G) : G ⧸ K) =
        QuotientGroup.mk (n * 1 : G) := rfl
    rw [hsmul, mul_one]
    rw [QuotientGroup.eq]
    simpa using hk
  have hstab : MulAction.stabilizer N b = K.subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff]
    rw [Subgroup.mem_subgroupOf]
    change (n : N) • (QuotientGroup.mk (1 : G) : G ⧸ K) =
      (QuotientGroup.mk (1 : G) : G ⧸ K) ↔ (n : G) ∈ K
    have hsmul : (n : N) • (QuotientGroup.mk (1 : G) : G ⧸ K) =
        QuotientGroup.mk ((n : G) * 1 : G) := rfl
    rw [hsmul, mul_one]
    rw [QuotientGroup.eq]
    simp
  have hindex : (MulAction.stabilizer N b).index = K.index := by
    rw [MulAction.index_stabilizer]
    rw [horbit, Set.ncard_univ]
    rfl
  rw [← hindex]
  rw [hstab, ← Subgroup.inf_subgroupOf_right, inf_comm]
  rfl

end CFSG.GorensteinWalter

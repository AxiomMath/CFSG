module

public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XLayer

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly

theorem isComponentOf_iff_of_normal_of_commutator_le {G : Type} [Group G] {H N K : Subgroup G}
    (hNH : N ≤ H)
    (hab : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ N) :
    IsComponentOf K H ↔ IsComponentOf K N := by
  have hn : (N.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * n * (g : G)⁻¹ * (n : G)⁻¹ ∈ N := hab g g.2 n n.2
    have h2 := N.mul_mem h1 hn
    rw [inv_mul_cancel_right] at h2
    exact h2
  rw [CFSG.Assembly.isComponentOf_iff_open, CFSG.Assembly.isComponentOf_iff_open]
  exact (CFSG.LocalAnalysis.GLTheoremA.S172X.isComponentOf_iff_of_commutator_le hNH hn
    (by rw [Subgroup.commutator_le]; intro a ha b hb; exact hab a ha b hb)).symm

end CFSG.StandardType.ClassicalPosition

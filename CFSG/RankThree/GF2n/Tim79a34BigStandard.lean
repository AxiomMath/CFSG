module

public import CFSG.RankThree.GF2n.Tim79a34BigBar

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isElemAbelian_wbar [Finite G] {M V Q P H : Subgroup G} (hH : BigEndHyp M V Q P H) :
    IsElemAbelian 2 (WbarM M V H) := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨w₁, hw₁, h₁⟩ := mem_WbarM_iff.mp x.2
    obtain ⟨w₂, hw₂, h₂⟩ := mem_WbarM_iff.mp y.2
    apply Subtype.ext
    show (x : Mbar M) * (y : Mbar M) = (y : Mbar M) * (x : Mbar M)
    rw [← h₁, ← h₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hc.wOf_isElemAbelian.comm hw₁ hw₂)
  · obtain ⟨w, hw, rfl⟩ := mem_WbarM_iff.mp hx
    rw [pow_two, ← QuotientGroup.mk_mul]
    have : w * w = 1 := Subtype.ext (hc.wOf_isElemAbelian.mul_self_eq_one hw)
    rw [this]
    rfl

theorem two_le_of_pow_eq {f q : ℕ} (h : 2 ^ f = q) (hq : 4 ≤ q) : 2 ≤ f := by
  by_contra hlt
  have h1 : f ≤ 1 := by omega
  have h2 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
  omega

end CFSG.RankThree.GF2n.Tim79a

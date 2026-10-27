module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

theorem XbarPre_le_normalizer_sup_comm {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) :
    XbarPre M Q Z B ≤
      Subgroup.normalizer ((Z ⊔ ⁅Q, XbarPre M Q Z B⁆ : Subgroup G) : Set G) := by
  intro s hs
  have hsM : (s : G) ∈ M := XbarPre_le_M hc hs
  rw [← conjSubgroup_eq_self_iff]
  have hZ : conjSubgroup (s : G) Z = Z := by
    rw [conjSubgroup_eq_self_iff]
    exact Subgroup.centralizer_le_normalizer (Z : Set G) (XbarPre_le_H0 hc hs).2
  have hQ : conjSubgroup (s : G) Q = Q := by
    rw [conjSubgroup_eq_self_iff]
    exact hc.hyp.Q_normal.2 hsM
  have hX : conjSubgroup (s : G) (XbarPre M Q Z B) = XbarPre M Q Z B :=
    XbarPre_normal hc hsM
  have hV : conjSubgroup (s : G) (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) =
      Z ⊔ ⁅Q, XbarPre M Q Z B⁆ := by
    rw [show conjSubgroup (s : G) (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) =
        conjSubgroup (s : G) Z ⊔ conjSubgroup (s : G) ⁅Q, XbarPre M Q Z B⁆ from by
      unfold conjSubgroup
      rw [Subgroup.map_sup]]
    rw [show conjSubgroup (s : G) ⁅Q, XbarPre M Q Z B⁆ =
        ⁅conjSubgroup (s : G) Q, conjSubgroup (s : G) (XbarPre M Q Z B)⁆ from by
      unfold conjSubgroup
      rw [Subgroup.map_commutator]]
    rw [hZ, hQ, hX]
  exact hV

theorem Z_subgroupOf_sup_comm_normal {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) :
    (Z.subgroupOf (Z ⊔ ⁅Q, XbarPre M Q Z B⁆)).Normal := by
  apply Subgroup.normal_of_le_center
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro v
  apply Subtype.ext
  have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
  have hZQ : Z ≤ Q := by
    rw [hc.hyp.hZ, cen_eq]
    exact inf_le_left
  have hvQ : (v : G) ∈ Q := (sup_le hZQ (commutator_le_Q hc)) v.2
  have hzC : (z : G) ∈ cen Q := hc.hyp.hZ ▸ hzZ
  rw [cen_eq] at hzC
  exact Subgroup.mem_centralizer_iff.mp hzC.2 (v : G) hvQ

end CFSG.RankThree.GF2n.Stroth80

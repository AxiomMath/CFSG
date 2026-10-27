module

public import CFSG.RankThree.GF2n.Stroth80.Sec11CM

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem Q_le_XbarPreCenter (hc : Ctx M Q Z B) : Q ≤ XbarPreCenter M Q Z B := by
  intro q hq
  have hqM : q ∈ M := by
    have hq' : q ∈ inSubgroup (pCore 2) M := hc.hyp.hQ ▸ hq
    exact Subgroup.map_subtype_le _ hq'
  refine Subgroup.mem_map.mpr ⟨⟨q, hqM⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  have hq' : (⟨q, hqM⟩ : ↥M) ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.mpr hq
  have hone : (QuotientGroup.mk' (Q.subgroupOf M)) ⟨q, hqM⟩ = 1 :=
    (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) _).mpr hq'
  rw [hone]
  exact Subgroup.one_mem _

end CFSG.RankThree.GF2n.Stroth80

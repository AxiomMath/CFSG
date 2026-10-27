module

public import CFSG.RankThree.GF2n.Stroth80.Sec35

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem mk'_mul_conj_eq_of_mem [(Q.subgroupOf M).Normal] {l y : ↥M} {k : ℕ}
    (hk : (l : G) * ((y : G) * l * (y : G)⁻¹) * ((y : G) ^ k * l * ((y : G) ^ k)⁻¹)⁻¹ ∈ Q) :
    QuotientGroup.mk' (Q.subgroupOf M) l * (QuotientGroup.mk' (Q.subgroupOf M) y *
      QuotientGroup.mk' (Q.subgroupOf M) l * (QuotientGroup.mk' (Q.subgroupOf M) y)⁻¹) =
    QuotientGroup.mk' (Q.subgroupOf M) y ^ k * QuotientGroup.mk' (Q.subgroupOf M) l *
      (QuotientGroup.mk' (Q.subgroupOf M) y ^ k)⁻¹ := by
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) (l * (y * l * y⁻¹) * (y ^ k * l * (y ^ k)⁻¹)⁻¹) =
      1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hk)
  simp only [map_mul, map_inv, map_pow] at h1
  exact mul_inv_eq_one.mp h1

variable [Finite G]

theorem Ctx.conj_mul_inv_mem_of_mul_conj_mem (hc : Ctx M Q Z B) {l y : G}
    (hl : l ∈ LB M Q B) (h : l * (y * l * y⁻¹) ∈ Q) : y ^ 1 * l * (y ^ 1)⁻¹ * l⁻¹ ∈ Q := by
  have h3 : l⁻¹ * (l * (y * l * y⁻¹)) * l ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 (M.inv_mem (hc.LB_le_M hl))) _).mp h
    rwa [inv_inv] at this
  have e : y ^ 1 * l * (y ^ 1)⁻¹ * l⁻¹ = (l⁻¹ * (l * (y * l * y⁻¹)) * l) * (l ^ 2)⁻¹ := by
    group
  rw [e]
  exact Q.mul_mem h3 (Q.inv_mem (hc.sq_mem_Q_of_mem_LB hl))

end CFSG.RankThree.GF2n.Stroth80

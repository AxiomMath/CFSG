module

public import CFSG.RankThree.GF2n.Stroth80.Sec34TI

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.conj_LB_eq_of_conj_BZ (hc : Ctx M Q Z B) {m r : G} (hm : m ∈ M) (hr : r ∈ M)
    (h : conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z) :
    conjSubgroup m (LB M Q B) = conjSubgroup r (LB M Q B) := by
  have hcr : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hr
  have hk : m * r⁻¹ ∈ M := M.mul_mem hm (M.inv_mem hr)
  have hle : conjSubgroup (m * r⁻¹) (conjSubgroup r B) ≤ conjSubgroup r B ⊔ Z := by
    rw [← conjSubgroup_mul, mul_assoc, inv_mul_cancel, mul_one, ← h]
    exact le_sup_left
  have key := hcr.conj_LB_eq_of_le_sup_Z hk hle
  rw [hc.LB_conj hr, ← conjSubgroup_mul, mul_assoc, inv_mul_cancel, mul_one] at key
  exact key

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.RankThree.PartOne.S11d.ThreeCompAssemble
public import CFSG.RankThree.PartOne.S11d.LowRank
public import CFSG.RankThree.PartOne.S11d.FieldFFTwo

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.TCX

variable {G : Type} [Group G] [Finite G]

theorem fieldFixedRankL_of_tags (hOdd : OddCenterLie) (hT : ∀ t, FixedRankTL t)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hHR : ∀ t, HighRankFalse t) : FieldFixedRank := by
  intro G _ _ p J u hset hup hrank h2
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hset.2.2.2.2.2.2.1
  obtain ⟨hp, hp5, hq, hEven, hrk, hZ, hfa⟩ := hset
  obtain ⟨he, c, hcC, hc1, hcp, huc⟩ := hrank
  have hp2 : p ≠ 2 := by omega
  have huJ : u ∉ J ⊔ Subgroup.centralizer (J : Set G) := hfa.2.1
  obtain ⟨t, n, f₀, hf₀, hM, hX⟩ := fieldAutT_of_inducesFieldAut hp hZ hu hup hfa
  have hLR2 := localRankLeTwo_of_evenRank he hp hp2 hZ hcC hc1 hcp
  have hLRA := localRankAut_of_evenRank he hp hp2 hZ hu hup huJ hcC hc1 hcp huc
  have hαinn : centerQuotientConj J ⟨u, hu⟩ ∉ innerAut (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨q', hq'⟩
    exact huJ (mem_sup_of_inner hq.1 hu hq'.symm)
  have h2T : 2 ≤ CFSG.pRank p (↥J ⧸ Subgroup.center ↥J) := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
      (Subgroup.center ↥J) hZ]
    exact h2
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥J) :=
    hOdd ↥J hq t n (p * f₀) (by nlinarith) hM
  have hLow : LowRank t n := by
    by_contra hnl
    exact hHR t hGA ↥J p n f₀ hq hp hp5 hf₀ hZ2 hZ ((Sec9A.evenRank_subgroup_le J).trans he) hM hnl
  rw [← pRank_fixRes_eq hp hZ hu hup]
  exact hT t _ p hp hp5 hLR2 h2T n f₀ hf₀ hM hLow _ (centerQuotientConj_pow hu hup) hαinn hLRA hX

end CFSG.RankThree.PartOne

module

public import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic
import CFSG.RankThree.GF2n.Tim81.Sec6.S61Class
import CFSG.RankThree.GF2n.Tim81.Sec6.S61Odd
import CFSG.RankThree.GF2n.Tim81.Sec6.S62Center
import CFSG.Quasithin.H13.NQCatSubnormalCore
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSetting

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

theorem Sec6Hyp.sigma_conj_m0 (hS : Sec6Hyp M V) {U U' : Subgroup G} (hU : U ∈ sigmaSet M V)
    (hU' : U' ∈ sigmaSet M V) : ∃ x ∈ m0Of M V, U' = conjSubgroup x U := by
  obtain ⟨g, rfl, hH⟩ := hU
  by_contra hcon
  exact hS.false_of_mem_restM0 ⟨g, rfl, hH⟩ (C := U') ⟨hU', fun h => hcon h⟩

theorem Sec6Hyp.pCore_imgQ_m0 (hS : Sec6Hyp M V) : pCore 2 ↥(imgQ M (m0Of M V)) = ⊥ := by
  have h := CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal' (p := 2)
    hS.sec5.imgQ_m0Of_normal.isSubnormal
  rw [CFSG.QuasithinUnique.Setup.Campbell.pCore_quotient_pCore_eq_bot' 2] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp
    (le_bot_iff.mp h)

theorem Sec6Hyp.oddCore_imgQ_m0_le_center (hS : Sec6Hyp M V) :
    pPrimeCore 2 ↥(imgQ M (m0Of M V)) ≤ Subgroup.center _ := by
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro z
  have h := Subgroup.mem_centralizer_iff.mp (hS.imgQ_m0Of_le_centralizer_oddCore z.2)
    (o : MBar M) ⟨o, ho, rfl⟩
  exact Subtype.ext h.symm

theorem Sec6Hyp.center_imgQ_lOf (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    imgQ M (lOf M V g) ⊓ Subgroup.centralizer (imgQ M (lOf M V g) : Set (MBar M)) =
      imgQ M (conjSubgroup g V) :=
  le_antisymm (hS.imgQ_lOf_inf_centralizer_le hg) (hS.sec5.imgQ_le_imgQ_lOf_inf_centralizer hg)

end CFSG.RankThree.GF2n.Tim81

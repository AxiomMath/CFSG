module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeOfQuasi
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeBar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixRootCentralizerSummandFlatInput_of_nbr (hSch : SchreierFor InCatalog)
    (hstrN : GGRootCentSummandStructNbrInput) (hKF : GGKGroupFusionLayerInputFlat)
    (h3 : GGRootCentAutKIIIFlatInput) (h4 : GGRootCentAutKIVFlatInput)
    (hexc : GGRootCentAutKNotExcInput) : GGSixRootCentralizerSummandFlatInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨𝒮, h𝒮, hcov⟩ := hstrN G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hfus := ggSixRootCentralizer_quotientFusion hctx hch
  have hEr := hch.le_centralizer
  obtain ⟨hEel, hEc⟩ := ggBarE_elem_card hp hp2 hEr hch.2.1
  have hEc' := hEc.trans hch.2.2.1
  have hr1 : r ≠ 1 := by
    intro h
    have h2 := hch.2.2.2.2.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hNtop := ggStepTwo_centralizer_ne_top hctx.1.2.1 hr1
  have hKP : KProper InCatalog G := hctx.1.2.2.1
  have hO2 := ggRCS_pCore_two_quot_eq_bot ↥(Subgroup.centralizer ({r} : Set G))
  have hOut : ∀ K : Subgroup (GGRCSNbar r), CFSG.IsComponent K →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    fun K hK => ggRCS_outer_solvable hKP hSch hNtop _ hK
  refine ⟨𝒮, fun S hS => ?_, hcov⟩
  rcases h𝒮 S hS with hQ | ⟨hp3, hS3', hNbr⟩
  · right
    obtain ⟨K, hK, hSK⟩ := ggRCS_exists_component hp2 hO2 hOut hfus hEel hEc' hQ
    have hKp : p ∣ Nat.card K := hQ.choose_spec.2.2.2.1.trans (Subgroup.card_dvd_of_le hSK)
    have hKc : IsComponentOf K ⊤ := ⟨le_top, (ggAssemblyIsSubnormal_iff le_top).mpr
      hK.2.subgroupOf,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hK.1⟩
    have hKO : ¬ K ≤ (QuotientGroup.mk' (LargeEvenPPrimeCore p (GGRCSNbar r))).ker := by
      rw [QuotientGroup.ker_mk']
      intro hle
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp CFSG.pPrimeCore_coprime_card
        (hKp.trans (Subgroup.card_dvd_of_le hle))
    have hKimg := ggIsComponentOf_map _ hKc hKO
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hKimg
    refine ⟨K, hSK, hKimg, fun hKV => ?_⟩
    have hEK := ggLemmaThreeThirteen_top hfus hEel hEc' hK hKp hKV
    have hset : GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S :=
      ⟨hK, hKV, hEK, hSK, hQ⟩
    exact ⟨hK, ggRCS_autKConfigFlat hp hfus hEel hEc' hEK hK
      (ggRCS_inCatalog_center_quot hKP hNtop _ hK) hQ hSK
      (h3 G p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset)
      (h4 G p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset)
      (hexc G p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset)⟩
  · left
    subst hp3
    obtain ⟨S₁, hS₁, e, he3, heM, heS⟩ := hNbr
    obtain ⟨ē, hēS, hē3, hcent⟩ := ggRCS_bar_data_of_centralizer_le he3 heM heS
    exact ggRCS_exists_normal_of_quasi hSch hKF h3 h4 hexc hctx s1 s2 hch rfl hS₁ hēS hē3
      hcent hS3'

end Inputs

end CFSG.StandardType

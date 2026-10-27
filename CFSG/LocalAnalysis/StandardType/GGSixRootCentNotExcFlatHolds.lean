module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcFlatDefs
public import CFSG.LocalAnalysis.StandardType.GGRCSShadowSmall
public import CFSG.LocalAnalysis.StandardType.GGRCSShadowSpRigid
public import CFSG.LocalAnalysis.StandardType.GGRCSShadowAlt
public import CFSG.LocalAnalysis.StandardType.GGRCSShadowFi22
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthAll

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Holds

theorem ggRootCentAutKNotExcFlatInput_holds : GGRootCentAutKNotExcFlatInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 hSch E r hch hcnt K S hset h3 h4 hN hsh
  classical
  have hK : CFSG.IsComponent K := hset.1
  have hKV := hset.2.1
  have hEK := hset.2.2.1
  have hSK := hset.2.2.2.1
  have hQ := hset.2.2.2.2
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
  have hcat := ggRCS_inCatalog_center_quot hKP hNtop _ hK
  have hker : (QuotientGroup.mk'
      ((ggRCSU (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K).subgroupOf
        (ggRCSImg r E ⊔ K))).ker ≤
      ((ggRCSImg r E ⊔ (K ⊓ ggRCSImg r (ggM p B x L D J))) ⊓
        Subgroup.centralizer (K : Set (GGRCSNbar r))).subgroupOf (ggRCSImg r E ⊔ K) := by
    intro w hw
    rw [QuotientGroup.ker_mk'] at hw
    exact hw
  have hlay := ggRCS_layer_ne_bot hp hfus.1 hQ hSK
  have hrest := ggHypThreeSixteenRestFlat_of_parts
    (ggRCS_hypRestII hfus hEel hEc' hEK hK hcat)
    (ggHypRestIIIFlat_of_ad (@h3 hN) hlay) (@h4 hN)
  have hI := ggAutK_hypOne hp hp2 hfus hEel hEc' hEK hKV
    (QuotientGroup.mk' ((ggRCSU (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K).subgroupOf
      (ggRCSImg r E ⊔ K))) (QuotientGroup.mk'_surjective _) hker
  have hyp : GGHypThreeSixteenFlat p
      (ggRCSTt (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K)
      (ggRCSEt (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K) := ⟨hI, hrest⟩
  have hEab : ∀ a ∈ ggRCSImg r E, ∀ b ∈ ggRCSImg r E, Commute a b := by
    intro a ha b hb
    refine ggRCS_commute_of_mem_map _ (fun u v => ?_) ha hb
    have h := hch.2.1.1.is_comm.comm (⟨u.1.1, u.2⟩ : ↥E) ⟨v.1.1, v.2⟩
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hperf : ∀ P : Subgroup (ggRCSWt (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K),
      ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting
        (ggRCSWt (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K) :=
    ggRCS_perfect_le_generalizedFitting hK hEK hEab
  have hKH := ggRCS_not_generalizedFitting_le hK hEK hEab hfus.1 hKV
  obtain ⟨F, hinj, hF⟩ := ggRCS_exists_componentInj_six hctx hSch hch hset
  obtain ⟨o, ho, htyped⟩ := hcnt
  have hbound : ∀ N, (CFSG.LieType.ChevTwo.compOrdSet
      ↥(ggRCSHK (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K) N).ncard ≤ o.count N :=
    fun N => (ncard_compOrdSet_le_of_injOn F hinj hF N).trans (htyped.2 N)
  unfold GGFusionException at hsh
  rcases hsh with ⟨hp3, he, -⟩ | ⟨hp5, ⟨s, hs2, hs4, he⟩, hrow⟩ | ⟨hCE, hrows⟩ |
      ⟨hp5, he, hrow⟩
  · exact ggShadow_false_altSix hyp hlay hperf hKH hp3 he
  · obtain ⟨C₁, C₂, hne, hC₁, hC₂, hc₁, hc₂⟩ :=
      ggShadow_alt_two_components hyp hKH hp5 hs2 hs4 he hrow
    exact ggSix_false_of_count_sixty hctx s1 hp5 ho
      ((two_le_ncard_compOrdSet hne hC₁ hC₂ hc₁ hc₂).trans (hbound 60))
  · rcases hrows with ⟨hp3, hK8, -⟩ | ⟨hp3, hK6, -⟩ | ⟨hp3, hK34, -⟩ | ⟨-, hSz, -⟩ |
        ⟨hp3, hL28, -⟩
    · obtain ⟨-, -, C, hC, hcard⟩ := ggShadow_spEight_component hyp hlay hperf hKH hp3 hK8
      have hrig := ggShadow_rigid_spEight hyp hlay hperf hKH hp3 hK8 hCE
      have hpos : 0 < o.count 174182400 :=
        lt_of_lt_of_le (by norm_num) ((one_le_ncard_compOrdSet hC hcard).trans (hbound _))
      obtain ⟨rfl, rfl, rfl⟩ := ggRootFactorOrders_mem_174182400 ho (List.count_pos_iff.mp hpos)
      obtain ⟨y, hyr, hy3, hyM, J₁, hJ₁y, hJ₁⟩ := ggRCSSix_yData_POmegaPlus hctx s1 s2 hp3 hch
      exact ggRCSSix_false_of_y hctx hSch hch hset hyp.2.1.1 ⟨C, hC⟩ hrig hyr hy3 hyM hJ₁y hJ₁
    · obtain ⟨-, -, C, hC, hcard⟩ := ggShadow_spSix_component hyp hlay hperf hKH hp3 hK6
      have hrig := ggShadow_rigid_spSix hyp hlay hperf hKH hp3 hK6 hCE
      have hpos : 0 < o.count 25920 :=
        lt_of_lt_of_le (by norm_num) ((one_le_ncard_compOrdSet hC hcard).trans (hbound _))
      rcases ggRootFactorOrders_mem_25920 ho (List.count_pos_iff.mp hpos) with
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · obtain ⟨y, hyr, hy3, hyM, J₁, hJ₁y, hJ₁⟩ :=
          ggRootCentOrthYSUInput_holds G p B Bs x L D J ψ hctx s1 s2 hp3 E r hch
        exact ggRCSSix_false_of_y hctx hSch hch hset hyp.2.1.1 ⟨C, hC⟩ hrig hyr hy3 hyM hJ₁y
          hJ₁
      · obtain ⟨y, hyr, hy3, hyM, J₁, hJ₁y, hJ₁⟩ :=
          ggRCSSix_yData_POmegaMinus hctx s1 s2 hp3 hch
        exact ggRCSSix_false_of_y hctx hSch hch hset hyp.2.1.1 ⟨C, hC⟩ hrig hyr hy3 hyM hJ₁y
          hJ₁
    · obtain ⟨C, hC, hcard⟩ := ggShadow_lThreeFour_component hyp hlay hperf hKH hp3 hK34
      have hpos : 0 < o.count 360 :=
        lt_of_lt_of_le (by norm_num) ((one_le_ncard_compOrdSet hC hcard).trans (hbound _))
      exact ggSix_false_of_mem_360 hctx s1 hp3 ho (List.count_pos_iff.mp hpos)
    · exact ggShadow_false_szThirtyTwo hyp hlay hperf hSz
    · exact ggShadow_false_lTwoEight hyp hlay hperf hKH hp3 hL28
  · obtain ⟨C, hC, hcard⟩ := ggShadow_fi22_component hyp hlay hperf hp5 he hrow
    have hpos : 0 < o.count 174182400 :=
      lt_of_lt_of_le (by norm_num) ((one_le_ncard_compOrdSet hC hcard).trans (hbound _))
    exact ggSix_false_of_mem_174182400 hctx s1 hp5 ho (List.count_pos_iff.mp hpos)

end Holds

end CFSG.StandardType

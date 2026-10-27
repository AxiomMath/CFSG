module

public import CFSG.Quasithin.Vol2.Ch9Sec3FFDB51
public import CFSG.Quasithin.Vol2.Ch9Sec3FFDMod
public import CFSG.Quasithin.Vol2.Ch9Sec3KX
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs

public section

namespace CFSG.Quasithin.H13.Ch9.FFB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem a314_bar (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts)
    {Y T K KY : Subgroup G} (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKY : K ≤ Y)
    (hKl : K ∈ lFamily T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hA : Nonempty (O2Q K ≃* alternatingGroup (Fin 5))) (hKYc : KY ∈ cComp Y) (hlt : K < KY) :
    modO2Image Y K < modO2Image Y KY ∧
      A314Statement (o2Img Y T) (modO2Image Y K) (modO2Image Y KY) := by
  have hne : modO2Image Y K ≠ modO2Image Y KY := fun h =>
    hlt.ne (Vol2.Ch11.SecA.eq_of_modO2Image_eq hT (le_of_mem_cComp hKYc) hlt.le
      (perfect_of_mem_cComp hKYc) hTK h)
  have hltbar : modO2Image Y K < modO2Image Y KY :=
    lt_of_le_of_ne (Subgroup.map_mono fun _ hx => hlt.le hx) hne
  refine ⟨hltbar, ?_⟩
  have hQbar := SQTKHyp.of_sqtkGroup ↥Y hSQ
  have hsylbar : IsSylowTwoOf (o2Img Y T) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT) _
      (QuotientGroup.mk'_surjective _)
  have hAbar : IsAlt 5 (↥(modO2Image Y K) ⧸ CFSG.solvableRadical ↥(modO2Image Y K)) :=
    A7.isAlt_quot_solvableRadical_of_surj hA (barMap_surjective hKY) (isPGroup_ker_barMap _)
  exact a314 h314 hQbar (h36 _ hQbar) (h312 _ hQbar) hsylbar (modO2Image_mem_lFamily hT hKY hKl)
    hAbar (modO2Image_mem_cComp hKYc) hltbar

theorem nonempty_o2q_equiv {Y KY : Subgroup G} (hSQ : SQTKGroup ↥Y) (hKYc : KY ∈ cComp Y)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) :
    Nonempty (O2Q KY ≃* ↥(modO2Image Y KY)) := by
  have hQbar := SQTKHyp.of_sqtkGroup ↥Y hSQ
  have hnorm : (KY.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hKYc)).mpr hYKY
  have hKYn : (modO2Image Y KY).Normal :=
    hnorm.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (QuotientGroup.mk'_surjective _)
  have hbot : CFSG.pCore 2 ↥(modO2Image Y KY) = ⊥ := pCore_eq_bot_of_normal hQbar.o2 hKYn
  obtain ⟨e1⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv (le_of_mem_cComp hKYc)
  exact ⟨e1.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)⟩

theorem autOn_facts (h56 : AsB56) {Y T K KY V : Subgroup G} [IsMulCommutative ↥V]
    (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKKY : K ≤ KY) (hKYc : KY ∈ cComp Y)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y V)
    (hperf : ⁅K, K⁆ = K) (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ ⁅K, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G))
    (hq : CFSG.IsQuasisimple (O2Q KY)) :
    CFSG.IsQuasisimple ↥(autOn KY V) ∧ B56QuasisimpleList ↥(autOn KY V) ∧
      60 ∣ Nat.card ↥(autOn KY V) ∧
      ∃ π : O2Q KY →* ↥(autOn KY V), Function.Surjective π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (V : Set G) := hKYY.trans hYV
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKKY.trans hKYN
  have hO2 : pCoreOf 2 (autOn Y V) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hle : autOn KY V ≤ autOn Y V := InternalSec.autOn_le_autOn_of_le hKYY
  have hn : ((autOn KY V).subgroupOf (autOn Y V)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hle).mpr fun k a hk ha => ?_
    exact InternalSec.autOn_normal_of (U := V) hYKY a ha k hk
  have hO2KY : pCoreOf 2 (autOn KY V) = ⊥ := by
    have h := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ hle hn
    rw [hO2] at h
    exact le_bot_iff.1 h
  have hJT : thompsonJ T ≤ Subgroup.normalizer (V : Set G) :=
    (iSup₂_le fun _ hA => hA.1).trans (hT.1.trans hYV)
  have hKV : ¬ K ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ (FFD.commutator_le_centralizer h hJT)
  have hnt : ¬ KY ≤ Subgroup.centralizer (V : Set G) := fun h => hKV (hKKY.trans h)
  have hqA : CFSG.IsQuasisimple ↥(autOn KY V) :=
    InternalSec.isQuasisimple_autOn hKYN hq hO2KY hnt
  obtain ⟨A, -, hA, hLA⟩ := FFD.exists_offender_of_commutator hVe hred hT hKYY hYKY hqA hKKY hJ
  have hV2 : ∀ w ∈ V, w ^ 2 = 1 := fun w hw => by simpa [pow_two] using hVe.2 w hw
  obtain ⟨hKJ, -, -, -, hcases⟩ :=
    InternalSec.b56Cases_ffJ_autOn h56 hV2 hYV hKYY hYKY hSQ hO2 hA hLA
  have hsnX : IsSubnormal (autOn KY V) (autOn Y V) :=
    A3.subnormal_map (conjAct V)
      (A3.subnormal_comap (Subgroup.normalizer (V : Set G)).subtype (subnormal_of_mem_cComp hKYc))
  have hlist := SBc3.b56QL_of_subnormal hKJ (A3.subnormal_of_le_of_le hsnX hKJ (B6.ffJ_le _))
    hqA hcases
  have h60 : 60 ∣ Nat.card ↥(autOn KY V) :=
    (FFD.card_autOn_dvd hKN hperf hA5 hKV).trans
      (Subgroup.card_dvd_of_le (InternalSec.autOn_le_autOn_of_le hKKY))
  exact ⟨hqA, hlist, h60, QuotientGroup.lift (CFSG.pCore 2 ↥KY) (InternalSec.autOnHom hKYN)
    (InternalSec.pCore_le_ker_autOnHom hKYN hO2KY),
    QuotientGroup.lift_surjective_of_surjective _ _ (InternalSec.autOnHom_surjective hKYN) _⟩

end CFSG.Quasithin.H13.Ch9.FFB

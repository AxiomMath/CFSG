module

public import CFSG.RankThree.PartTwo.Sec14.Wales1418Off
public import CFSG.RankThree.PartTwo.Sec4.Item41PRankNarrow41
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.RankThree.PartTwo.Sec14.Liebeck1418BridgeFix
import CFSG.RankThree.PartTwo.Sec14.Liebeck1418BridgeSz
import CFSG.RankThree.PartTwo.Sec14.Liebeck1418BridgeComp
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PBasic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotCentralizer)
open Proof1418Res3 (ActsTrivOnLayer3)
open scoped commutatorElement

theorem step1418OffBridgeR_of_lift (h45 : Sec4.Item4_5)
    (hlift : ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X →
      ∀ K : Subgroup (X ⧸ CFSG.pPrimeCore 3 X), IsComponent K →
        ∃ J ∈ thetaComponents 3 X, J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = K) :
    Step1418OffBridgeR := by
  intro G _ _ A c L S B b E R h hnt
  set H := Subgroup.centralizer (E : Set G) with hHdef
  set O := CFSG.pPrimeCore 3 ↥H with hO
  obtain ⟨K, hK, r, hrR, hrK⟩ : ∃ K : Subgroup (↥H ⧸ O), IsComponent K ∧ ∃ r : ↥H, (r : G) ∈ R ∧
      QuotientGroup.mk' O r ∉ Subgroup.centralizer (K : Set (↥H ⧸ O)) := by
    by_contra hall
    push Not at hall
    apply hnt
    rintro _ ⟨r, hr, rfl⟩
    have hle : layer (↥H ⧸ O) ≤
        Subgroup.centralizer (Subgroup.zpowers (QuotientGroup.mk' O r) : Set (↥H ⧸ O)) := by
      rw [layer.eq_sSup]
      refine sSup_le fun K hK => ?_
      exact Subgroup.le_centralizer_iff.mp
        (Subgroup.zpowers_le.mpr (hall K hK r (Subgroup.mem_subgroupOf.mp hr)))
    exact Subgroup.le_centralizer_iff.mp hle (Subgroup.mem_zpowers _)
  obtain ⟨J₀, hJ₀, hJ₀K⟩ := hlift ↥H (off_sectionFourHyp_centralizer h) K hK
  set J := J₀.map H.subtype with hJdef
  have hJ : J ∈ thetaComponentsIn H := ⟨J₀, hJ₀, rfl⟩
  obtain ⟨hAJ, hRJ⟩ := off_le_normalizer_of_mem_thetaComponentsIn h h45 J hJ
  refine ⟨J, hJ, hAJ, hRJ, fun hRθ => hrK ?_⟩
  have h1 : ⁅J, R⁆ ≤ inSubgroup (aschbacherSolvableCore 3) J :=
    (Sec6.commutator_le_theta_iff hRJ).mpr hRθ
  have hJH : J ≤ H := Subgroup.map_subtype_le J₀
  have hJsub : CFSG.Open.IsSubnormal J H :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hJH).mpr (mem_thetaComponentsIn_iff.mp hJ).2.2.1
  have h2 : inSubgroup (aschbacherSolvableCore 3) J ≤ CFSG.GH74.GLS.pPrimeCoreOf 3 H :=
    Sec15.Proof155P.inSubgroup_theta_le_pPrimeCoreOf hJsub
  rw [← hJ₀K, Subgroup.mem_centralizer_iff]
  rintro _ ⟨j, hj, rfl⟩
  have hjr : ⁅(j : G), (r : G)⁆ ∈ CFSG.GH74.GLS.pPrimeCoreOf 3 H :=
    h2 (h1 (Subgroup.commutator_mem_commutator ⟨j, hj, rfl⟩ hrR))
  obtain ⟨o, ho, hoeq⟩ := hjr
  have hoj : o = ⁅j, r⁆ := Subtype.ext (by simpa [commutatorElement_def] using hoeq)
  rw [hoj] at ho
  have h3 : ⁅QuotientGroup.mk' O j, QuotientGroup.mk' O r⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr ho
  exact (commutatorElement_eq_one_iff_commute.mp h3).eq

theorem exists_mem_thetaComponents_map_eq {X : Type} [Group X]
    [Finite X] (hX : SectionFourHyp X) (hSz : KFacts.KPSz) (h41 : Sec4.Item4_1PRankLargePrime)
    {K : Subgroup (X ⧸ CFSG.pPrimeCore 3 X)} (hK : IsComponent K) :
    ∃ J ∈ thetaComponents 3 X, J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = K :=
  exists_mem_thetaComponents_map_eq_of_four hX hSz
    (fun D S _ Y hY hinj hs h5 h2 => false_of_four_components hX h41 Y hY hinj hs h5 h2) hK

theorem step1418OffBridgeR_of (h45 : Sec4.Item4_5)
    (hSz : KFacts.KPSz) (h41 : Sec4.Item4_1PRankLargePrime) : Step1418OffBridgeR :=
  step1418OffBridgeR_of_lift h45 fun X _ _ hX _ hK =>
    exists_mem_thetaComponents_map_eq hX hSz h41 hK

end CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge

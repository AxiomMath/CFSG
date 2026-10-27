module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieBorelTorus
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientTools
public import CFSG.GroupTheory.NormalizerQuotientQuotient
public import CFSG.GroupTheory.NormalizerQuotientOddCover
public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCoverUncond
public import CFSG.Adapters.LinearCatalog
public import CFSG.GH74.KGroups.PSLN
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsF4
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Main
public import CFSG.LieType.Chevalley.BorelSelfNormalizer
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
public import CFSG.LieType.Ree.SuzukiBorelStructure
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28Parabolic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291R3ExDef
public import CFSG.ClassicalGroups.Orthogonal.BorelQuotientAbelian
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSp
public import CFSG.Quasithin.Background.C22PfG
public import CFSG.Quasithin.SteinbergBIEvenLinearThreeThreeSylowAction
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagTriangular
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
import CFSG.LocalAnalysis.ComponentInitial.BorelQuotientAbelian
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwo
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.SteinbergBICommonNormalizerTools
public import CFSG.Quasithin.SteinbergBITwoThreeSL2
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint
open CFSG.LieType.Ree
open scoped commutatorElement

@[expose] def KBorelFamily (t : CFSG.Open.StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (m f : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 f → LieModel (K ⧸ Subgroup.center K) t m 2 f →
    CFSG.Open.IsQuasisimple K →
    ∀ S : Subgroup K, IsSylowTwoOf S ⊤ → IsMulCommutative (normalizerQuotient S)

@[expose] def K_BorelTorusAbelian_PSL : Prop := KBorelFamily .PSL

@[expose] def K_BorelTorusAbelian_PSU : Prop := KBorelFamily .PSU

@[expose] def K_BorelTorusAbelian_PSp : Prop := KBorelFamily .PSp

@[expose] def K_BorelTorusAbelian_POmegaOdd : Prop := KBorelFamily .POmegaOdd

@[expose] def K_BorelTorusAbelian_POmegaPlus : Prop := KBorelFamily .POmegaPlus

@[expose] def K_BorelTorusAbelian_POmegaMinus : Prop := KBorelFamily .POmegaMinus

@[expose] def K_BorelTorusAbelian_G2 : Prop := KBorelFamily .G2

@[expose] def K_BorelTorusAbelian_F4 : Prop := KBorelFamily .F4

@[expose] def K_BorelTorusAbelian_E6 : Prop := KBorelFamily .E6

@[expose] def K_BorelTorusAbelian_E7 : Prop := KBorelFamily .E7

@[expose] def K_BorelTorusAbelian_E8 : Prop := KBorelFamily .E8

@[expose] def K_BorelTorusAbelian_twistedE6 : Prop := KBorelFamily .twistedE6

@[expose] def K_BorelTorusAbelian_trialityD4 : Prop := KBorelFamily .trialityD4

@[expose] def K_BorelTorusAbelian_twistedB2 : Prop := KBorelFamily .twistedB2

@[expose] def K_BorelTorusAbelian_twistedG2 : Prop := KBorelFamily .twistedG2

@[expose] def K_BorelTorusAbelian_twistedF4 : Prop := KBorelFamily .twistedF4

@[expose] def K_BorelTorusAbelian_Tits : Prop := KBorelFamily .Tits

theorem k_BorelTorusAbelian_of_families
    (hPSL : K_BorelTorusAbelian_PSL) (hPSU : K_BorelTorusAbelian_PSU)
    (hPSp : K_BorelTorusAbelian_PSp) (hPOmegaOdd : K_BorelTorusAbelian_POmegaOdd)
    (hPOmegaPlus : K_BorelTorusAbelian_POmegaPlus)
    (hPOmegaMinus : K_BorelTorusAbelian_POmegaMinus) (hG2 : K_BorelTorusAbelian_G2)
    (hF4 : K_BorelTorusAbelian_F4) (hE6 : K_BorelTorusAbelian_E6)
    (hE7 : K_BorelTorusAbelian_E7) (hE8 : K_BorelTorusAbelian_E8)
    (htwistedE6 : K_BorelTorusAbelian_twistedE6)
    (htrialityD4 : K_BorelTorusAbelian_trialityD4)
    (htwistedB2 : K_BorelTorusAbelian_twistedB2)
    (htwistedG2 : K_BorelTorusAbelian_twistedG2)
    (htwistedF4 : K_BorelTorusAbelian_twistedF4) (hTits : K_BorelTorusAbelian_Tits) :
    K_BorelTorusAbelian := by
  intro K _ _ t m f hadm hmodel hq S hS
  cases t
  · exact hPSL K m f hadm hmodel hq S hS
  · exact hPSU K m f hadm hmodel hq S hS
  · exact hPSp K m f hadm hmodel hq S hS
  · exact hPOmegaOdd K m f hadm hmodel hq S hS
  · exact hPOmegaPlus K m f hadm hmodel hq S hS
  · exact hPOmegaMinus K m f hadm hmodel hq S hS
  · exact hG2 K m f hadm hmodel hq S hS
  · exact hF4 K m f hadm hmodel hq S hS
  · exact hE6 K m f hadm hmodel hq S hS
  · exact hE7 K m f hadm hmodel hq S hS
  · exact hE8 K m f hadm hmodel hq S hS
  · exact htwistedE6 K m f hadm hmodel hq S hS
  · exact htrialityD4 K m f hadm hmodel hq S hS
  · exact htwistedB2 K m f hadm hmodel hq S hS
  · exact htwistedG2 K m f hadm hmodel hq S hS
  · exact htwistedF4 K m f hadm hmodel hq S hS
  · exact hTits K m f hadm hmodel hq S hS

theorem k_BorelTorusAbelian_POmegaOdd : K_BorelTorusAbelian_POmegaOdd := by
  intro K _ _ m f hadm _ _ S _
  simp [CFSG.Open.StatedLieAdmissible] at hadm

theorem k_BorelTorusAbelian_twistedG2 : K_BorelTorusAbelian_twistedG2 := by
  intro K _ _ m f hadm _ _ S _
  simp [CFSG.Open.StatedLieAdmissible] at hadm

@[expose] def KBorelSimple (t : CFSG.Open.StatedLieTag) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (m f : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 f → LieModel Y t m 2 f →
    ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ → IsMulCommutative (normalizerQuotient S)

theorem k_BorelSimple_G2 :
    KBorelSimple .G2 := by
  intro Y _ _ m f hadm hY S hS
  obtain ⟨rfl, -⟩ := (LieModel.chevalleyExceptional_iff (t := .G2) (by decide)).1 hY
  refine isMulCommutative_normalizerQuotient_g2 ?_ hY S hS
  have h := hadm
  simp [CFSG.Open.StatedLieAdmissible] at h
  omega

theorem k_BorelSimple_trialityD4 :
    KBorelSimple .trialityD4 := by
  intro Y _ _ m f hadm hY S hS
  obtain ⟨rfl, -⟩ :=
    (LieModel.chevalleyExceptional_iff (t := .trialityD4) (by decide)).1 hY
  obtain ⟨-, hX⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hY (by decide)
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hX
  have hmodfin : Finite (CFSG.Blueprint.Chevalley.ModGL TwistTag.D4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨H, F, D⟩ :=
    (CFSG.Quasithin.H13.Sec53F.TriD4.borelAutData_d4 σ hf hK hσ).exists_of_equiv e hS
  exact IsMulCommutative.mk (Std.Commutative.mk D.quot_comm)

theorem k_BorelSimple_twistedF4 :
    KBorelSimple .twistedF4 := by
  intro Y _ _ m f hadm hY S hS
  obtain ⟨rfl, -⟩ := (LieModel.reeTits_iff (t := .twistedF4) (by decide)).1 hY
  have hf2 : 2 ≤ f := by
    have h := hadm
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  have hpar : CFSG.Quasithin.H13.IsSec53Param .twistedF4 0 f :=
    ⟨hf2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
  obtain ⟨H, F, D⟩ := CFSG.Quasithin.H13.Sec53F.lieBorelFacts_f4 Y f hpar hY S hS
  exact IsMulCommutative.mk (Std.Commutative.mk D.quot_comm)

@[expose] def oddMultiplierFreeTags : Finset CFSG.Open.StatedLieTag :=
  {.PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus, .G2, .F4, .E7, .E8, .trialityD4, .twistedB2,
    .twistedG2, .twistedF4, .Tits}

@[expose] def K_BorelTorusAbelian_centerTwo : Prop :=
  ∀ (t : CFSG.Open.StatedLieTag), t ∈ oddMultiplierFreeTags →
    ∀ (K : Type) [Group K] [Finite K] (m f : ℕ),
      CFSG.Open.StatedLieAdmissible t m 2 f →
      LieModel (K ⧸ Subgroup.center K) t m 2 f →
      CFSG.Open.IsQuasisimple K → IsPGroup 2 (Subgroup.center K)

theorem k_BorelTorusAbelian_of_simple_of_centerTwo (t : CFSG.Open.StatedLieTag)
    (ht : t ∈ oddMultiplierFreeTags) (hsimple : KBorelSimple t)
    (hcenter : K_BorelTorusAbelian_centerTwo) : KBorelFamily t := by
  intro K _ _ m f hadm hY hq S hS
  have hZ2 : IsPGroup 2 (Subgroup.center K) := hcenter t ht K m f hadm hY hq
  have hZle : Subgroup.center K ≤ S :=
    hS.le_of_normalizes le_top (by simp [Subgroup.normalizer_eq_top]) hZ2
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker ≤ S := by
    rw [QuotientGroup.ker_mk']
    exact hZle
  have hS' : IsSylowTwoOf (S.map (QuotientGroup.mk' (Subgroup.center K))) ⊤ := by
    refine ⟨le_top, hS.isPGroup.map _, ?_⟩
    have hidx : (S.map (QuotientGroup.mk' (Subgroup.center K))).index = S.index :=
      Subgroup.index_map_eq S (QuotientGroup.mk'_surjective _) hker
    have hSidx : ¬ 2 ∣ S.index := by
      rw [← Subgroup.relIndex_top_right (H := S)]
      exact hS.2.2
    rw [show ((S.map (QuotientGroup.mk' (Subgroup.center K))).subgroupOf ⊤).index =
      (S.map (QuotientGroup.mk' (Subgroup.center K))).index from
      Subgroup.relIndex_top_right _]
    rw [hidx]
    exact hSidx
  have hcomm : IsMulCommutative
      (normalizerQuotient (S.map (QuotientGroup.mk' (Subgroup.center K)))) :=
    hsimple (K ⧸ Subgroup.center K) m f hadm hY _ hS'
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
    (CFSG.GroupTheory.normalizerQuotient_quotientEquiv (Subgroup.center K) S hZle).symm hcomm

theorem k_BorelTorusAbelian_G2
    (hcenter : K_BorelTorusAbelian_centerTwo) : K_BorelTorusAbelian_G2 :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .G2 (by decide) k_BorelSimple_G2 hcenter

theorem k_BorelTorusAbelian_trialityD4
    (hcenter : K_BorelTorusAbelian_centerTwo) : K_BorelTorusAbelian_trialityD4 :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .trialityD4 (by decide)
    k_BorelSimple_trialityD4 hcenter

theorem k_BorelTorusAbelian_twistedF4
    (hcenter : K_BorelTorusAbelian_centerTwo) : K_BorelTorusAbelian_twistedF4 :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .twistedF4 (by decide)
    k_BorelSimple_twistedF4 hcenter

theorem k_BorelSimple_chevalley_aux {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hU : IsSylowTwoOf (posUnipotentSub τ K) ⊤) :
    IsMulCommutative (normalizerQuotient (posUnipotentSub τ K)) := by
  set N := Subgroup.normalizer (posUnipotentSub τ K : Set (adjointGroup τ K)) with hN
  have hcore : CFSG.Open.pCore 2 ↥N = (posUnipotentSub τ K).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalizer)]
    exact CFSG.AGLEmbedding.L28Parabolic.pCoreOf_normalizer_eq hU
  have hcomm :=
    CFSG.ClassicalGroups.Orthogonal.isMulCommutative_normalizer_posUnipotent_quotient_pCore
      (τ := τ) (K := K)
  have hle : _root_.commutator ↥N ≤ CFSG.Open.pCore 2 ↥N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  rw [hcore] at hle
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle

theorem k_BorelSimple_untwisted_chevalley_aux
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hcard : Nat.card K = 2 ^ f)
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* AdjointQuotient τ K)
    (S : Subgroup Y) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  have hU : IsSylowTwoOf (posUnipotentSub τ K) ⊤ := by
    obtain ⟨hUp, hUi⟩ := CFSG.LieType.Chevalley.isPGroup_and_not_dvd_index
      (τ := τ) (K := K) 2 (posUnipotent_le_adjointGroup (K := K))
      (card_posUnipotent (τ := τ) (K := K))
    refine ⟨le_top, hUp, ?_⟩
    rw [show ((posUnipotentSub τ K).subgroupOf ⊤).index = (posUnipotentSub τ K).index from
      Subgroup.relIndex_top_right _]
    exact hUi
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let e' : Y ≃* ↥(adjointGroup τ K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf e' hS hU
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eN.symm
    (k_BorelSimple_chevalley_aux hU)

theorem k_BorelSimple_untwisted_chevalley
    {τ : Tag} {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (hmodel : CFSG.Blueprint.UntwistedChevalleyModel Y τ (2 ^ f))
    (S : Subgroup Y) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  obtain ⟨K, hfield, hfin, hcard, ⟨e⟩⟩ := hmodel
  have hf1 : 1 ≤ f := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
    rcases Nat.eq_zero_or_pos f with h0 | hpos
    · rw [h0, pow_zero] at hcard
      omega
    · exact hpos
  exact @k_BorelSimple_untwisted_chevalley_aux
   
    τ K hfield hfin
    (@CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.charP_of_card_eq_prime_pow K hfield hfin
      2 f ⟨Nat.prime_two⟩ hf1 hcard) f hcard Y _ _ e S hS

theorem k_BorelSimple_F4 :
    KBorelSimple .F4 := by
  intro Y _ _ m f hadm hY S hS
  obtain ⟨rfl, hmodel⟩ := (LieModel.chevalleyExceptional_iff (t := .F4) (by decide)).1 hY
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hmodel
  exact k_BorelSimple_untwisted_chevalley hmodel.2 S hS

theorem k_BorelSimple_E7 :
    KBorelSimple .E7 := by
  intro Y _ _ m f hadm hY S hS
  obtain ⟨rfl, hmodel⟩ := (LieModel.chevalleyExceptional_iff (t := .E7) (by decide)).1 hY
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hmodel
  exact k_BorelSimple_untwisted_chevalley hmodel.2 S hS

theorem k_BorelSimple_E8 :
    KBorelSimple .E8 := by
  intro Y _ _ m f hadm hY S hS
  obtain ⟨rfl, hmodel⟩ := (LieModel.chevalleyExceptional_iff (t := .E8) (by decide)).1 hY
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel] at hmodel
  exact k_BorelSimple_untwisted_chevalley hmodel.2 S hS

theorem k_BorelSimple_suzuki_aux {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsMulCommutative (normalizerQuotient (suzukiU a K)) := by
  obtain ⟨-, hTcomm, -, hTN, hUT, hBUT, -, -⟩ := suzuki_borel_structure (a := a) hK
  have hN : Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) = suzukiB a K :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwr1_sz_normalizer hK
  have hcommT : IsMulCommutative (suzukiT a K) :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (hTcomm x x.2 y y.2)
  have hUH : ∀ x ∈ suzukiU a K, x ∈ suzukiT a K → x = 1 := by
    intro x hxU hxT
    have hx : x ∈ suzukiU a K ⊓ suzukiT a K := Subgroup.mem_inf.2 ⟨hxU, hxT⟩
    rw [hUT] at hx
    exact Subgroup.mem_bot.mp hx
  have hB : ∀ g ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)),
      ∃ u ∈ suzukiU a K, ∃ h ∈ suzukiT a K, g = u * h := by
    intro g hg
    rw [hN] at hg
    change g ∈ (suzukiB a K : Set (suzukiGroup a K)) at hg
    rw [hBUT, Set.mem_mul] at hg
    obtain ⟨u, hu, t, ht, hut⟩ := hg
    exact ⟨u, hu, t, ht, hut.symm⟩
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_complement hTN hUH hB
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eN.symm hcommT

theorem k_BorelSimple_twistedB2 : KBorelSimple .twistedB2 := by
  intro Y _ _ m f hadm hY S hS
  obtain ⟨rfl, hm⟩ := LieModel.suzukiModel hY
  obtain ⟨-, a, ha, K, _, _, hf, hKcard, ⟨e⟩⟩ := hm
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hKcard, hf]
  obtain ⟨P, hP⟩ : ∃ P : Sylow 2 (suzukiGroup a K),
      (P : Subgroup (suzukiGroup a K)) = suzukiU a K :=
    ⟨CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwr1_sz_sylow hK',
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwr1_sz_sylow_coe hK'⟩
  have hUsyl : IsSylowTwoOf (suzukiU a K) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hP]
      exact P.isPGroup'
    · rw [← hP]
      rw [show ((P : Subgroup (suzukiGroup a K)).subgroupOf ⊤).index =
        (P : Subgroup (suzukiGroup a K)).index from Subgroup.relIndex_top_right _]
      exact P.not_dvd_index
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf e hS hUsyl
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eN.symm
    (k_BorelSimple_suzuki_aux ha hK')

theorem k_BorelTorusAbelian_F4
    (hcenter : K_BorelTorusAbelian_centerTwo) : K_BorelTorusAbelian_F4 :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .F4 (by decide) k_BorelSimple_F4 hcenter

theorem k_BorelTorusAbelian_E7
    (hcenter : K_BorelTorusAbelian_centerTwo) : K_BorelTorusAbelian_E7 :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .E7 (by decide) k_BorelSimple_E7 hcenter

theorem k_BorelTorusAbelian_E8
    (hcenter : K_BorelTorusAbelian_centerTwo) : K_BorelTorusAbelian_E8 :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .E8 (by decide) k_BorelSimple_E8 hcenter

theorem k_BorelTorusAbelian_twistedB2
    (hcenter : K_BorelTorusAbelian_centerTwo) : K_BorelTorusAbelian_twistedB2 :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .twistedB2 (by decide)
    k_BorelSimple_twistedB2 hcenter

theorem genericOrders_eq_one_of_mem_oddMultiplierFreeTags
    {t : CFSG.Open.StatedLieTag} {m f : ℕ} (ht : t ∈ oddMultiplierFreeTags)
    (hadm : CFSG.Open.StatedLieAdmissible t m 2 f) :
    CFSG.Blueprint.Multiplier.genericOrders t m 2 f = (1, 1) := by
  have hf : 1 ≤ f := by
    have h := hadm
    simp only [CFSG.Open.StatedLieAdmissible] at h
    exact h.2.1
  have h2 : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    CFSG.LocalAnalysis.RankThreeUC.S15.ksm_gcd_two_odd
      (CFSG.LocalAnalysis.RankThreeUC.S15.ksm_odd_two_pow_sub_one hf)
  cases t
  · simp [oddMultiplierFreeTags] at ht
  · simp [oddMultiplierFreeTags] at ht
  · simp only [CFSG.Blueprint.Multiplier.genericOrders]
    rw [h2]
  · simp [CFSG.Open.StatedLieAdmissible] at hadm
  · simp only [CFSG.Blueprint.Multiplier.genericOrders]
    rw [if_pos (Nat.even_pow.2 ⟨even_two, by omega⟩)]
  · simp only [CFSG.Blueprint.Multiplier.genericOrders]
    congr 1
    have hm : 1 ≤ m := by
      have h := hadm
      simp only [CFSG.Open.StatedLieAdmissible] at h
      omega
    exact CFSG.LocalAnalysis.RankThreeUC.S15.ksm_gcd_four_odd
      (by
        rw [← pow_mul]
        exact (Nat.even_pow.2 ⟨even_two, Nat.mul_ne_zero (by omega) (by omega)⟩).add_one)
  · rfl
  · rfl
  · simp [oddMultiplierFreeTags] at ht
  · simp only [CFSG.Blueprint.Multiplier.genericOrders]
    rw [h2]
  · rfl
  · simp [oddMultiplierFreeTags] at ht
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem k_BorelTorusAbelian_centerTwo_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_BorelTorusAbelian_centerTwo := by
  intro t ht K _ _ m f hadm hM hq
  have hgen := genericOrders_eq_one_of_mem_oddMultiplierFreeTags ht hadm
  have hperf : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  obtain ⟨-, ⟨eM⟩⟩ := hN (K ⧸ Subgroup.center K) t m 2 f hM
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.ksm_exc_two t m f
  have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic t m 2 f ×
      CFSG.Blueprint.Multiplier.exceptional t m 2 f) = 2 ^ k := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_card_table_eq, hgen, hk]
    ring
  have hM' : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (K ⧸ Subgroup.center K)) = 2 ^ k := by
    rw [← hcard, ← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      (K ⧸ Subgroup.center K)).toEquiv]
    exact Nat.card_congr eM.toEquiv
  have hdvd := @CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20r_card_center_dvd_hopf
    K (K ⧸ Subgroup.center K) _ _ hperf (MulEquiv.refl _)
  rw [hM'] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.of_card (n := j) hj

theorem k_BorelSimple_PSp_aux {Y : Type} [Group Y] [Finite Y] {m f : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hadm : CFSG.Open.StatedLieAdmissible .PSp m 2 f)
    (e : Y ≃* StatedSp m K) (S : Subgroup Y) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  have hm : 1 ≤ m := by
    have h := hadm
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  obtain ⟨P, hP⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent (K := K) 2 m
  have hU : IsSylowTwoOf
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent m K) ⊤ := by
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf e hS hU
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eN.symm
    (CFSG.GroupTheory.isMulCommutative_normalizerQuotient_of_borel
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.sylow_normalizers (K := K) 2 hm).1
      fun _ hx _ hy =>
        CFSG.AGLEmbedding.ParabAutIrr.commutator_mem_unipotent (r := m) (K := K) hx hy)

theorem k_BorelSimple_PSp : KBorelSimple .PSp := by
  intro Y _ _ m f hadm hY S hS
  obtain ⟨K, hfield, hfin, hchar, hcard, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel hY
  exact @k_BorelSimple_PSp_aux Y _ _ m f K hfield hfin hchar hadm e S hS

theorem center_isPGroup_two_of_genericOrders_eq_one
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess)
    {t : CFSG.Open.StatedLieTag} {K : Type} [Group K] [Finite K] {m f : ℕ}
    (hgen : CFSG.Blueprint.Multiplier.genericOrders t m 2 f = (1, 1))
    (hM : LieModel (K ⧸ Subgroup.center K) t m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) :
    IsPGroup 2 (Subgroup.center K) := by
  have hperf : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  obtain ⟨-, ⟨eM⟩⟩ := hN (K ⧸ Subgroup.center K) t m 2 f hM
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.ksm_exc_two t m f
  have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic t m 2 f ×
      CFSG.Blueprint.Multiplier.exceptional t m 2 f) = 2 ^ k := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_card_table_eq, hgen, hk]
    ring
  have hM' : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (K ⧸ Subgroup.center K)) = 2 ^ k := by
    rw [← hcard, ← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      (K ⧸ Subgroup.center K)).toEquiv]
    exact Nat.card_congr eM.toEquiv
  have hdvd := @CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20r_card_center_dvd_hopf
    K (K ⧸ Subgroup.center K) _ _ hperf (MulEquiv.refl _)
  rw [hM'] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.of_card (n := j) hj

theorem k_BorelTorusAbelian_PSp
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_BorelTorusAbelian_PSp :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .PSp (by decide) k_BorelSimple_PSp
    (k_BorelTorusAbelian_centerTwo_of_griess hN)

theorem k_BorelSimple_PSL_aux {Y : Type} [Group Y] [Finite Y] {m f : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hadm : CFSG.Open.StatedLieAdmissible .PSL m 2 f)
    (e : Y ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m K)
    (S : Subgroup Y) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  have hm : 1 ≤ m := by
    have h := hadm
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  obtain ⟨P, hP⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
      (K := K) (n := m) 2 hm
  have hU : IsSylowTwoOf
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projUnitriangular m K) ⊤ := by
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf e hS hU
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eN.symm
    (CFSG.LocalAnalysis.ComponentInitial.isMulCommutative_normalizerQuotient_projUnitriangular hm)

theorem k_BorelSimple_PSL : KBorelSimple .PSL := by
  intro Y _ _ m f hadm hY S hS
  obtain ⟨K, hfield, hfin, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hY
  exact @k_BorelSimple_PSL_aux Y _ _ m f K hfield hfin
    (@CFSG.SeitzReduction.LinearPilot.charP_two_of_card_eq_two_pow K hfield f hcard)
    hadm e S hS

theorem k_BorelSimple_PSU_aux {Y : Type} [Group Y] [Finite Y] {m f : ℕ} {K : Type}
    [Field K] [Finite K] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    {r ε : ℕ} (hε : ε ≤ 1) (hm : 2 * r + ε = m) (hm3 : 3 ≤ m)
    (e : Y ≃* CFSG.ClassicalGroups.UnitaryFlag.hypPSU h r ε)
    (S : Subgroup Y) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  have hr : 1 ≤ r := by omega
  obtain ⟨P, hP⟩ :=
    (CFSG.ClassicalGroups.UnitaryFlag.unitary_order_and_Sylow h hr hε).2.2.2.2.1
  have hU : IsSylowTwoOf
      (CFSG.ClassicalGroups.UnitaryFlag.hypProjUnitriangular h r ε) ⊤ := by
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf e hS hU
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eN.symm
    (CFSG.LocalAnalysis.ComponentInitial.isMulCommutative_normalizerQuotient_hypProjUnitriangular
      h hr hε)

theorem k_BorelSimple_PSU : KBorelSimple .PSU := by
  intro Y _ _ m f hadm hY S hS
  let r := m / 2
  let ε := m % 2
  have hε : ε ≤ 1 := by
    have := Nat.mod_lt m (by norm_num : 0 < 2)
    omega
  have hm_eq : 2 * r + ε = m := by
    have := Nat.div_add_mod m 2
    simp only [r, ε]
    omega
  have hm3 : 3 ≤ m := by
    have h := hadm
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  have hf1 : 1 ≤ f := by
    have h := hadm
    simp [CFSG.Open.StatedLieAdmissible] at h
    exact h.2.1
  obtain ⟨K, hfield, hfin, h, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_hypPSU
      (Y := Y) (n := f) (r := r) (ε := ε) hf1 (by omega) (by rwa [hm_eq])
  exact @k_BorelSimple_PSU_aux Y _ _ m f K hfield hfin h r ε hε hm_eq hm3 e S hS

theorem k_BorelSimple_Tits :
    KBorelSimple .Tits := by
  intro Y _ _ m f hadm hY S hS
  have hSidx : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_top_right (H := S)]
    exact hS.2.2
  let P : Sylow 2 Y := hS.isPGroup.toSylow hSidx
  have hP : (P : Subgroup Y) = S := rfl
  have hN : Subgroup.normalizer (S : Set Y) ≤ S := by
    have h := CFSG.Quasithin.C22Pf.titsSylowSelfNormalizing_holds Y m f hY P
    rwa [hP] at h
  have hNeq : Subgroup.normalizer (S : Set Y) = S :=
    le_antisymm hN Subgroup.le_normalizer
  refine CFSG.GroupTheory.isMulCommutative_normalizerQuotient_of_borel hNeq ?_
  intro b hb b' hb'
  rw [commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem hb hb') (S.inv_mem hb)) (S.inv_mem hb')

theorem k_BorelTorusAbelian_Tits
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_BorelTorusAbelian_Tits :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .Tits (by decide) k_BorelSimple_Tits
    (k_BorelTorusAbelian_centerTwo_of_griess hN)

theorem k_BorelFamily_of_odd_cover {G K : Type} [Group G] [Finite G] [Group K] [Finite K]
    (α : G →* K) (hα : Function.Surjective α) (hodd : Odd (Nat.card α.ker))
    {B U : Subgroup G} (hU : IsSylowTwoOf U ⊤)
    (hNB : Subgroup.normalizer (U : Set G) = B)
    (hcomm : ∀ b ∈ B, ∀ b' ∈ B, ⁅b, b'⁆ ∈ U)
    (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  have hP0 : IsSylowTwoOf (U.map α) ⊤ := CFSG.Quasithin.A312.isSylowTwoOf_top_map α hα hU
  have hcomm0 : IsMulCommutative (normalizerQuotient (U.map α)) :=
    CFSG.GroupTheory.isMulCommutative_normalizerQuotient_of_odd_cover α hα hodd hU hNB hcomm
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf (MulEquiv.refl K) hS hP0
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eN.symm hcomm0

theorem k_BorelTorusAbelian_PSL_cover_aux {K : Type} [Group K] [Finite K] {m f : ℕ}
    {F : Type} [Field F] [Finite F] [CharP F 2] (hm3 : 3 ≤ m) (hf3 : 3 ≤ f)
    (hF : Nat.card F = 2 ^ f)
    (e : K ⧸ Subgroup.center K ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m F)
    (hq : CFSG.Open.IsQuasisimple K) (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hk : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  obtain ⟨α, hα, hαc⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_slCover
      (m := m') (by omega) hk hq e
  have hkerOdd : Odd (Nat.card α.ker) := by
    have hle : α.ker ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (m' + 1) F := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
      exact hαc
    have hcard : Nat.card α.ker =
        Nat.card (α.ker.subgroupOf
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (m' + 1) F)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv |>.symm
    have hdvd1 : Nat.card (α.ker.subgroupOf
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (m' + 1) F)) ∣
        Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (m' + 1) F) :=
      Subgroup.card_subgroup_dvd_card _
    have hdvd2 : Nat.card
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (m' + 1) F) ∣
        Nat.card F - 1 :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd (by omega)
    have hoddF : Odd (Nat.card F - 1) := by
      rw [hF]
      exact CFSG.LocalAnalysis.RankThreeUC.S15.ksm_odd_two_pow_sub_one (by omega)
    have hdvd : Nat.card α.ker ∣ Nat.card F - 1 := by
      rw [hcard]
      exact hdvd1.trans hdvd2
    exact Odd.of_dvd_nat hoddF hdvd
  obtain ⟨P, hP⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
      (K := F) (n := m' + 1) 2 (by omega)
  have hU : IsSylowTwoOf
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular (m' + 1) F) ⊤ := by
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hNB : Subgroup.normalizer
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular (m' + 1) F :
        Set (Matrix.SpecialLinearGroup (Fin (m' + 1)) F)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular (m' + 1) F :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.sylow_normalizers
      (K := F) 2 (by omega)).1
  have hcomm : ∀ b ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular
      (m' + 1) F,
      ∀ b' ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular (m' + 1) F,
        ⁅b, b'⁆ ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular (m' + 1) F := by
    intro b hb b' hb'
    have h := CFSG.Quasithin.SteinbergBI.commutator_mem_unitriangular (K := F) hb hb'
    simpa [commutatorElement_def] using h
  exact k_BorelFamily_of_odd_cover α hα hkerOdd hU hNB hcomm S hS

theorem k_BorelTorusAbelian_PSL_cover {K : Type} [Group K] [Finite K] {m f : ℕ}
    (hm3 : 3 ≤ m) (hf3 : 3 ≤ f)
    (hL : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  exact @k_BorelTorusAbelian_PSL_cover_aux K _ _ m f F hfield hfin
    (@CFSG.SeitzReduction.LinearPilot.charP_two_of_card_eq_two_pow F hfield f hF)
    hm3 hf3 hF e hq S hS

theorem isMulCommutative_of_simple_of_centerTwo_at (t : CFSG.Open.StatedLieTag)
    {K : Type} [Group K] [Finite K] {m f : ℕ}
    (hsimple : KBorelSimple t)
    (hZ2 : IsPGroup 2 (Subgroup.center K))
    (hL : LieModel (K ⧸ Subgroup.center K) t m 2 f)
    (hq : CFSG.Open.IsQuasisimple K)
    (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  have hZle : Subgroup.center K ≤ S :=
    hS.le_of_normalizes le_top (by simp [Subgroup.normalizer_eq_top]) hZ2
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker ≤ S := by
    rw [QuotientGroup.ker_mk']
    exact hZle
  have hS' : IsSylowTwoOf (S.map (QuotientGroup.mk' (Subgroup.center K))) ⊤ := by
    refine ⟨le_top, hS.isPGroup.map _, ?_⟩
    have hidx : (S.map (QuotientGroup.mk' (Subgroup.center K))).index = S.index :=
      Subgroup.index_map_eq S (QuotientGroup.mk'_surjective _) hker
    have hSidx : ¬ 2 ∣ S.index := by
      rw [← Subgroup.relIndex_top_right (H := S)]
      exact hS.2.2
    rw [show ((S.map (QuotientGroup.mk' (Subgroup.center K))).subgroupOf ⊤).index =
      (S.map (QuotientGroup.mk' (Subgroup.center K))).index from
      Subgroup.relIndex_top_right _]
    rw [hidx]
    exact hSidx
  have hcomm : IsMulCommutative
      (normalizerQuotient (S.map (QuotientGroup.mk' (Subgroup.center K)))) :=
    hsimple (K ⧸ Subgroup.center K) m f (CFSG.Blueprint.LieModel.admissible hL) hL _ hS'
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
    (CFSG.GroupTheory.normalizerQuotient_quotientEquiv (Subgroup.center K) S hZle).symm hcomm

theorem k_BorelTorusAbelian_PSU_cover
    {K : Type} [Group K] [Finite K] {m f : ℕ}
    (hf2 : 2 ≤ f) (hm3 : 3 ≤ m)
    (hL : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  let r := m / 2
  let ε := m % 2
  have hε : ε ≤ 1 := by
    have := Nat.mod_lt m (by norm_num : 0 < 2)
    omega
  have hm_eq : 2 * r + ε = m := by
    have := Nat.div_add_mod m 2
    simp only [r, ε]
    omega
  have hL' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU (2 * r + ε) 2 f := by
    rwa [hm_eq]
  obtain ⟨F, _, _, h, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_hypPSU
      (Y := K ⧸ Subgroup.center K) (n := f) (r := r) (ε := ε) (by omega) (by omega) hL'
  obtain ⟨α, hα, hker_le, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_cover
      h hε (by omega) hf2 hq e
  have hkerOdd : Odd (Nat.card α.ker) := by
    have hle : α.ker ≤ CFSG.ClassicalGroups.UnitaryFlag.hypScalars h r ε := hker_le
    have hcard : Nat.card α.ker =
        Nat.card (α.ker.subgroupOf (CFSG.ClassicalGroups.UnitaryFlag.hypScalars h r ε)) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
    have hdvd1 : Nat.card (α.ker.subgroupOf
        (CFSG.ClassicalGroups.UnitaryFlag.hypScalars h r ε)) ∣
        Nat.card (CFSG.ClassicalGroups.UnitaryFlag.hypScalars h r ε) :=
      Subgroup.card_subgroup_dvd_card _
    have hdvd2 : Nat.card (CFSG.ClassicalGroups.UnitaryFlag.hypScalars h r ε) ∣ 2 ^ f + 1 := by
      rw [CFSG.ClassicalGroups.UnitaryFlag.card_hypScalars h (by omega)]
      exact Nat.gcd_dvd_right _ _
    have hodd : Odd (2 ^ f + 1) :=
      (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    have hdvd : Nat.card α.ker ∣ 2 ^ f + 1 := by
      rw [hcard]
      exact hdvd1.trans hdvd2
    exact Odd.of_dvd_nat hodd hdvd
  have hr : 1 ≤ r := by omega
  obtain ⟨P, hP⟩ :=
    (CFSG.ClassicalGroups.UnitaryFlag.unitary_order_and_Sylow h hr hε).2.1
  have hU : IsSylowTwoOf
      (CFSG.ClassicalGroups.UnitaryFlag.hypUnitriangular h r ε) ⊤ := by
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hNB : Subgroup.normalizer
      (CFSG.ClassicalGroups.UnitaryFlag.hypUnitriangular h r ε :
        Set (CFSG.ClassicalGroups.UnitaryFlag.hypSU h r ε)) =
      CFSG.ClassicalGroups.UnitaryFlag.hypBorel h r ε :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular h hr hε
  have hcomm : ∀ b ∈ CFSG.ClassicalGroups.UnitaryFlag.hypBorel h r ε,
      ∀ b' ∈ CFSG.ClassicalGroups.UnitaryFlag.hypBorel h r ε,
        ⁅b, b'⁆ ∈ CFSG.ClassicalGroups.UnitaryFlag.hypUnitriangular h r ε :=
    fun b hb b' hb' =>
      CFSG.GroupTheory.commutator_mem_of_diag_ker
        (CFSG.ClassicalGroups.UnitaryFlag.hypDiagHom h r ε hε)
        (CFSG.ClassicalGroups.UnitaryFlag.ker_hypDiagHom hε) hb hb'
  exact k_BorelFamily_of_odd_cover α hα hkerOdd hU hNB hcomm S hS

theorem k_BorelTorusAbelian_PSU_of_cover_or_gcd
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess)
    {K : Type} [Group K] [Finite K] {m f : ℕ}
    (hL : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (S : Subgroup K) (hS : IsSylowTwoOf S ⊤)
    (hgood : 2 ≤ f ∨ Nat.gcd m 3 = 1) :
    IsMulCommutative (normalizerQuotient S) := by
  have hm3 : 3 ≤ m := by
    have h := CFSG.Blueprint.LieModel.admissible hL
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  by_cases hf2 : 2 ≤ f
  · exact k_BorelTorusAbelian_PSU_cover hf2 hm3 hL hq S hS
  · have hf1 : f = 1 := by
      have h := CFSG.Blueprint.LieModel.admissible hL
      simp [CFSG.Open.StatedLieAdmissible] at h
      omega
    subst hf1
    have hgcd : Nat.gcd m 3 = 1 := by
      rcases hgood with h | h
      · omega
      · exact h
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU m 2 1 = (1, 1) := by
      simp [CFSG.Blueprint.Multiplier.genericOrders, hgcd]
    have hZ2 : IsPGroup 2 (Subgroup.center K) :=
      center_isPGroup_two_of_genericOrders_eq_one hN hgen hL hq
    exact isMulCommutative_of_simple_of_centerTwo_at .PSU k_BorelSimple_PSU hZ2 hL hq S hS

@[expose] def K_L34OddCover : Prop :=
  ∀ (K : Type) [Group K] [Finite K]
    [(CFSG.Open.pCoreOf 2 (Subgroup.center K)).Normal],
    CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL 3 2 2 →
    CFSG.Open.IsQuasisimple K →
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (α : Matrix.SpecialLinearGroup (Fin 3) F →*
        (K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center K))),
      Nat.card F = 4 ∧ Function.Surjective α ∧
      α.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) ∧
      Odd (Nat.card α.ker)

@[expose] def K_SU2OddCover : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (m : ℕ)
    [(CFSG.Open.pCoreOf 2 (Subgroup.center K)).Normal],
    3 ≤ m → 3 ∣ m →
    CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU m 2 1 →
    CFSG.Open.IsQuasisimple K →
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
      (r ε : ℕ), ε ≤ 1 ∧ 2 * r + ε = m ∧
      ∃ α : CFSG.ClassicalGroups.UnitaryFlag.hypSU h r ε →*
        (K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center K)),
        Function.Surjective α ∧
        α.ker ≤ CFSG.ClassicalGroups.UnitaryFlag.hypScalars h r ε ∧
        Odd (Nat.card α.ker)

theorem k_BorelTorusAbelian_PSL_of_cover_or_center
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess)
    {K : Type} [Group K] [Finite K] {m f : ℕ}
    (hL : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (S : Subgroup K) (hS : IsSylowTwoOf S ⊤)
    (hgood : 3 ≤ f ∨ m = 2 ∨ f = 1 ∨ ¬ 3 ∣ m) :
    IsMulCommutative (normalizerQuotient S) := by
  have hcenterPath : ∀ (hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL m 2 f = (1, 1)),
      IsMulCommutative (normalizerQuotient S) := by
    intro hgen
    exact isMulCommutative_of_simple_of_centerTwo_at .PSL k_BorelSimple_PSL
      (center_isPGroup_two_of_genericOrders_eq_one hN hgen hL hq) hL hq S hS
  by_cases hf3 : 3 ≤ f
  · by_cases hm3 : 3 ≤ m
    · exact k_BorelTorusAbelian_PSL_cover hm3 hf3 hL hq S hS
    · have hm2 : m = 2 := by
        have h := CFSG.Blueprint.LieModel.admissible hL
        simp [CFSG.Open.StatedLieAdmissible] at h
        omega
      subst hm2
      refine hcenterPath ?_
      have hf1 : 1 ≤ f := by
        have h := CFSG.Blueprint.LieModel.admissible hL
        simp [CFSG.Open.StatedLieAdmissible] at h
        omega
      have hodd : Odd (2 ^ f - 1) :=
        CFSG.LocalAnalysis.RankThreeUC.S15.ksm_odd_two_pow_sub_one hf1
      simp only [CFSG.Blueprint.Multiplier.genericOrders]
      rw [CFSG.LocalAnalysis.RankThreeUC.S15.ksm_gcd_two_odd hodd]
  · by_cases hm2 : m = 2
    · subst hm2
      refine hcenterPath ?_
      have hf1 : 1 ≤ f := by
        have h := CFSG.Blueprint.LieModel.admissible hL
        simp [CFSG.Open.StatedLieAdmissible] at h
        omega
      have hodd : Odd (2 ^ f - 1) :=
        CFSG.LocalAnalysis.RankThreeUC.S15.ksm_odd_two_pow_sub_one hf1
      simp only [CFSG.Blueprint.Multiplier.genericOrders]
      rw [CFSG.LocalAnalysis.RankThreeUC.S15.ksm_gcd_two_odd hodd]
    · by_cases hf1 : f = 1
      · subst hf1
        refine hcenterPath ?_
        simp [CFSG.Blueprint.Multiplier.genericOrders]
      · have hf2 : f = 2 := by
          have h := CFSG.Blueprint.LieModel.admissible hL
          simp [CFSG.Open.StatedLieAdmissible] at h
          omega
        subst hf2
        have hnot3 : ¬ 3 ∣ m := by
          rcases hgood with h | h | h | h
          · omega
          · exact absurd h hm2
          · exact absurd h hf1
          · exact h
        have hgcd : Nat.gcd m 3 = 1 := by
          have hdvd3 : Nat.gcd m 3 ∣ 3 := Nat.gcd_dvd_right _ _
          have hg1or3 : Nat.gcd m 3 = 1 ∨ Nat.gcd m 3 = 3 := by
            have := (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdvd3
            simpa using this
          rcases hg1or3 with h1 | h3
          · exact h1
          · exact absurd (h3 ▸ Nat.gcd_dvd_left m 3) hnot3
        refine hcenterPath ?_
        simp only [CFSG.Blueprint.Multiplier.genericOrders]
        norm_num
        rw [hgcd]

theorem k_BorelTorusAbelian_PSL_q4_cover {K : Type} [Group K] [Finite K] {n : ℕ}
    (hn3 : 3 ≤ n)
    (hL : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL (n + 1) 2 2)
    (hq : CFSG.Open.IsQuasisimple K) (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) := by
  let Q : TauCeti.PrimePower := ⟨2, 2, by norm_num, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A n Q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by exact Nat.le_trans (by norm_num : 1 ≤ 3) hn3,
      by norm_num [Q, TauCeti.PrimePower.card_def]⟩, ?_⟩
    rintro (⟨h, hq⟩ | ⟨h, hq⟩ | ⟨h, hq⟩) <;>
      · have h4 : Q.card = 4 := by norm_num [Q, TauCeti.PrimePower.card_def]
        omega
  have hF4 : Nat.card (GaloisField 2 2) = 2 ^ 2 :=
    GaloisField.card 2 2 (by norm_num)
  have e1 : K ⧸ Subgroup.center K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n + 1)) (GaloisField 2 2) :=
    (CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel
      (K := K ⧸ Subgroup.center K) (F := GaloisField 2 2)
      (n + 1) 2 2 (by norm_num) hF4 hL).some
  have e4 : (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.A n Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n + 1)) (GaloisField 2 2) :=
    CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n Q hv
  have e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.A n Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group :=
    e1.trans e4.symm
  obtain ⟨F, _, _, _, π, hFcard, hπ, hπc⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_central_cover_specialLinear_of_ne_two_four
      hq n (by omega) Q (by rfl) hv e (by omega)
  have hkerOdd : Odd (Nat.card π.ker) := by
    have hle : π.ker ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (n + 1) F := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
      exact hπc
    have hcard : Nat.card π.ker =
        Nat.card (π.ker.subgroupOf
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (n + 1) F)) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
    have hdvd1 : Nat.card (π.ker.subgroupOf
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (n + 1) F)) ∣
        Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (n + 1) F) :=
      Subgroup.card_subgroup_dvd_card _
    have hdvd2 : Nat.card
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (n + 1) F) ∣ Nat.card F - 1 :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd (by omega)
    have hodd : Odd (Nat.card F - 1) := by
      have h4 : Nat.card F = 4 := by simpa [Q] using hFcard
      rw [h4]
      norm_num
    have hdvd : Nat.card π.ker ∣ Nat.card F - 1 := by
      rw [hcard]
      exact hdvd1.trans hdvd2
    exact Odd.of_dvd_nat hodd hdvd
  obtain ⟨P, hP⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
      (K := F) (n := n + 1) 2 (by omega)
  have hU : IsSylowTwoOf
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular (n + 1) F) ⊤ := by
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hNB : Subgroup.normalizer
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular (n + 1) F :
        Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular (n + 1) F :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.sylow_normalizers
      (K := F) 2 (by omega)).1
  have hcomm : ∀ b ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular
      (n + 1) F,
      ∀ b' ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular (n + 1) F,
        ⁅b, b'⁆ ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular (n + 1) F := by
    intro b hb b' hb'
    have h := CFSG.Quasithin.SteinbergBI.commutator_mem_unitriangular (K := F) hb hb'
    simpa [commutatorElement_def] using h
  exact k_BorelFamily_of_odd_cover π hπ hkerOdd hU hNB hcomm S hS

theorem k_BorelTorusAbelian_PSL
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess)
    (hL34 : K_L34OddCover) : K_BorelTorusAbelian_PSL := by
  intro K _ _ m f hadm hL hq S hS
  by_cases hgood : 3 ≤ f ∨ m = 2 ∨ f = 1 ∨ ¬ 3 ∣ m
  · exact k_BorelTorusAbelian_PSL_of_cover_or_center hN hL hq S hS hgood
  · push Not at hgood
    obtain ⟨hf3, hm2, hf1', h3m⟩ := hgood
    have hf1 : 1 ≤ f := by
      have h := CFSG.Blueprint.LieModel.admissible hL
      simp [CFSG.Open.StatedLieAdmissible] at h
      omega
    have hf2 : f = 2 := by omega
    subst hf2
    have hm3 : 3 ≤ m := by
      have h := CFSG.Blueprint.LieModel.admissible hL
      simp [CFSG.Open.StatedLieAdmissible] at h
      omega
    by_cases hm4 : 4 ≤ m
    · have hm' : m - 1 + 1 = m := by omega
      have hL' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL (m - 1 + 1) 2 2 := by
        rwa [hm']
      exact k_BorelTorusAbelian_PSL_q4_cover (n := m - 1) (by omega) hL' hq S hS
    · have hm_eq : m = 3 := by omega
      subst hm_eq
      let O := CFSG.Open.pCoreOf 2 (Subgroup.center K)
      have hOcenter : O ≤ Subgroup.center K := by
        rintro x ⟨y, -, rfl⟩
        exact y.2
      have hOnormal : O.Normal := Subgroup.normal_of_le_center hOcenter
      have hO2 : IsPGroup 2 O :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.center K))).map
          (Subgroup.center K).subtype
      obtain ⟨F, _, _, _, α, hF, hα, hαc, hαodd⟩ :=
        @hL34 K _ _ hOnormal hL hq
      obtain ⟨P, hP⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
          (K := F) (n := 3) 2 (by norm_num)
      have hU : IsSylowTwoOf
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F) ⊤ := by
        rw [← hP]
        exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
      have hNB : Subgroup.normalizer
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F :
            Set (Matrix.SpecialLinearGroup (Fin 3) F)) =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 3 F :=
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.sylow_normalizers
          (K := F) 2 (by norm_num)).1
      have hcomm : ∀ b ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 3 F,
          ∀ b' ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 3 F,
            ⁅b, b'⁆ ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F := by
        intro b hb b' hb'
        have h := CFSG.Quasithin.SteinbergBI.commutator_mem_unitriangular (K := F) hb hb'
        simpa [commutatorElement_def] using h
      have hS' : IsSylowTwoOf (S.map (QuotientGroup.mk' O)) ⊤ :=
        CFSG.Quasithin.A312.isSylowTwoOf_top_map (QuotientGroup.mk' O)
          (QuotientGroup.mk'_surjective O) hS
      have hLcomm : IsMulCommutative
          (normalizerQuotient (S.map (QuotientGroup.mk' O))) :=
        k_BorelFamily_of_odd_cover α hα hαodd hU hNB hcomm
          (S.map (QuotientGroup.mk' O)) hS'
      exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
        (CFSG.GroupTheory.normalizerQuotient_quotientEquiv O S
          (hS.le_of_normalizes le_top (by simp [Subgroup.normalizer_eq_top]) hO2)).symm hLcomm

theorem k_BorelTorusAbelian_PSU
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess)
    (hSU2 : K_SU2OddCover) : K_BorelTorusAbelian_PSU := by
  intro K _ _ m f hadm hL hq S hS
  have hm3 : 3 ≤ m := by
    have h := CFSG.Blueprint.LieModel.admissible hL
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  by_cases hf2 : 2 ≤ f
  · exact k_BorelTorusAbelian_PSU_cover hf2 hm3 hL hq S hS
  · have hf1 : f = 1 := by
      have h := CFSG.Blueprint.LieModel.admissible hL
      simp [CFSG.Open.StatedLieAdmissible] at h
      omega
    subst hf1
    by_cases hgcd : Nat.gcd m 3 = 1
    · exact k_BorelTorusAbelian_PSU_of_cover_or_gcd hN hL hq S hS (Or.inr hgcd)
    · have h3m : 3 ∣ m := by
        have hdvd : Nat.gcd m 3 ∣ 3 := Nat.gcd_dvd_right _ _
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdvd with h1 | h3
        · exact absurd h1 hgcd
        · exact h3 ▸ Nat.gcd_dvd_left m 3
      let O := CFSG.Open.pCoreOf 2 (Subgroup.center K)
      have hOcenter : O ≤ Subgroup.center K := by
        rintro x ⟨y, -, rfl⟩
        exact y.2
      have hOnormal : O.Normal := Subgroup.normal_of_le_center hOcenter
      have hO2 : IsPGroup 2 O :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.center K))).map
          (Subgroup.center K).subtype
      obtain ⟨F, _, _, h, r, ε, hε, hm_eq, α, hα, hαle, hαodd⟩ :=
        @hSU2 K _ _ m hOnormal hm3 h3m hL hq
      have hr : 1 ≤ r := by omega
      obtain ⟨P, hP⟩ :=
        (CFSG.ClassicalGroups.UnitaryFlag.unitary_order_and_Sylow h hr hε).2.1
      have hU : IsSylowTwoOf
          (CFSG.ClassicalGroups.UnitaryFlag.hypUnitriangular h r ε) ⊤ := by
        rw [← hP]
        exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
      have hNB : Subgroup.normalizer
          (CFSG.ClassicalGroups.UnitaryFlag.hypUnitriangular h r ε :
            Set (CFSG.ClassicalGroups.UnitaryFlag.hypSU h r ε)) =
          CFSG.ClassicalGroups.UnitaryFlag.hypBorel h r ε :=
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular h hr hε
      have hcomm : ∀ b ∈ CFSG.ClassicalGroups.UnitaryFlag.hypBorel h r ε,
          ∀ b' ∈ CFSG.ClassicalGroups.UnitaryFlag.hypBorel h r ε,
            ⁅b, b'⁆ ∈ CFSG.ClassicalGroups.UnitaryFlag.hypUnitriangular h r ε :=
        fun b hb b' hb' =>
          CFSG.GroupTheory.commutator_mem_of_diag_ker
            (CFSG.ClassicalGroups.UnitaryFlag.hypDiagHom h r ε hε)
            (CFSG.ClassicalGroups.UnitaryFlag.ker_hypDiagHom hε) hb hb'
      have hS' : IsSylowTwoOf (S.map (QuotientGroup.mk' O)) ⊤ :=
        CFSG.Quasithin.A312.isSylowTwoOf_top_map (QuotientGroup.mk' O)
          (QuotientGroup.mk'_surjective O) hS
      have hLcomm : IsMulCommutative
          (normalizerQuotient (S.map (QuotientGroup.mk' O))) :=
        k_BorelFamily_of_odd_cover α hα hαodd hU hNB hcomm
          (S.map (QuotientGroup.mk' O)) hS'
      exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
        (CFSG.GroupTheory.normalizerQuotient_quotientEquiv O S
          (hS.le_of_normalizes le_top (by simp [Subgroup.normalizer_eq_top]) hO2)).symm hLcomm

theorem k_BorelTorusAbelian_of_griess_of_L34_SU2_orthogonal_E6
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess)
    (hL34 : K_L34OddCover) (hSU2 : K_SU2OddCover)
    (hPOmegaPlus : K_BorelTorusAbelian_POmegaPlus)
    (hPOmegaMinus : K_BorelTorusAbelian_POmegaMinus)
    (hE6 : K_BorelTorusAbelian_E6) (htwistedE6 : K_BorelTorusAbelian_twistedE6) :
    K_BorelTorusAbelian := by
  have hcenter := k_BorelTorusAbelian_centerTwo_of_griess hN
  exact k_BorelTorusAbelian_of_families
    (k_BorelTorusAbelian_PSL hN hL34) (k_BorelTorusAbelian_PSU hN hSU2)
    (k_BorelTorusAbelian_PSp hN) k_BorelTorusAbelian_POmegaOdd hPOmegaPlus hPOmegaMinus
    (k_BorelTorusAbelian_G2 hcenter) (k_BorelTorusAbelian_F4 hcenter) hE6
    (k_BorelTorusAbelian_E7 hcenter) (k_BorelTorusAbelian_E8 hcenter) htwistedE6
    (k_BorelTorusAbelian_trialityD4 hcenter) (k_BorelTorusAbelian_twistedB2 hcenter)
    k_BorelTorusAbelian_twistedG2 (k_BorelTorusAbelian_twistedF4 hcenter)
    (k_BorelTorusAbelian_Tits hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

module

public import CFSG.LocalAnalysis.StandardType.GGStdSpSixExcl
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.StandardType.GGF4OrderThreeLabel
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.LieType.ChevTwo.OrthogonalAutLarge
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeAltSix
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFam
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderSpAux1
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelC
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentLSide
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts2
public import CFSG.LocalAnalysis.ComponentInitial.KnownFourGroupDiagonalPump
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.SpTwoThreeFixedPoints
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.StandardType.GGR4Lemma47c
public import CFSG.LocalAnalysis.StandardType.GGR4AutInn
public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGResILineBThree
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8A
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Alt
public import CFSG.LocalAnalysis.StandardType.GGB48OmReduce
public import CFSG.LocalAnalysis.StandardType.GGResF4ExactTwo
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetCard
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetRank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1BC
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs196
public import CFSG.RankThree.PartTwo.Sec8.Hering611RSp62Inner
public import CFSG.LocalAnalysis.StandardType.GGR4JNCCard
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvT2
public import CFSG.LocalAnalysis.StandardType.GGPZMultCore
public import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitSC
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import Certificates.Certificate3088
public import Certificates.Certificate2151
public import Certificates.Certificate2152
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2158
public import Certificates.Certificate2161
public import Certificates.Certificate2162
public import Certificates.Certificate3008
public import Certificates.Certificate10010
public import Certificates.Certificate10011
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.LargeExtraspecial.S8CBFCrit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnAPI
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.Milestones.ASVolI.F48.Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofList
public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofPSL2
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofTwo

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResSmallSpThreeExactTwo_false
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 3) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  obtain ⟨lab, hlab, R, instR, I, F, θ, hsimple, hna, hP, hm⟩ :=
    largeEvenMarking_exists_markedModel hM
  have hp3 : p = 3 := hP.1.1
  subst hp3
  have hMono : GGInnerDiagOnLabel GGLabSp6 3 Bs L :=
    largeEvenMarking_mono (fun lab R _ I F θ hQ => by
      obtain ⟨-, htag, hn1, hr⟩ := hQ.1
      exact ⟨⟨htag, hr, hn1⟩, hQ.2⟩) hM
  exact not_ggInnerDiagOnLabel_sp6 hH.1 hMono

open CFSG.Assembly CFSG.Open
open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.SmallIdent
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

theorem ggHasLabel_sp62 : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel)
    CFSG.Sporadic.Co2Smith.Sp62 := by
  have hbot : StatedScalars (Fin 3 ⊕ Fin 3) (ZMod 2) = ⊥ :=
    CFSG.LieType.ChevTwo.AutLarge.statedScalars_zmodTwo
  have hmodel : CFSG.Open.StatedClassicalModel CFSG.Sporadic.Co2Smith.Sp62 .PSp 3 2 1 := by
    refine ⟨by norm_num [StatedLieAdmissible], ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
    exact ⟨(CFSG.Monster.Existence.Compat.statedProjEquivOfBot
      (StatedSp 3 (ZMod 2)) hbot).symm⟩
  exact ggHasLabel_C_of_statedClassicalModel hmodel

theorem ggHasLabel_psp43 : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
    CFSG.GH74.Exceptional.PSp43 := by
  have hmodel : CFSG.Open.StatedClassicalModel CFSG.GH74.Exceptional.PSp43 .PSU 4 2 1 := by
    refine ⟨by norm_num [StatedLieAdmissible], CFSG.Blueprint.Fischer.K,
      inferInstance, inferInstance, ?_, ?_⟩
    · exact CFSG.Fischer.Classification.Unitary.card_K
    · exact ⟨CFSG.GH74.Exceptional.psp43EquivU2.trans
        CFSG.GH74.Exceptional.u2FourEquiv⟩
  dsimp only [GGHasLabel, LargeEvenRawDatum]
  exact recipeUnitary_of_statedClassicalModel hmodel

theorem sp8_order_three_component_labels {s : StatedSp 4 (ZMod 2)}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) {J : Subgroup (StatedSp 4 (ZMod 2))}
    (hJ : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))))) :
    GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) ∨
      GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) ∨
      GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) := by
  classical
  obtain ⟨hcat, hA6⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.sp8_comp
      CFSG.LocalAnalysis.GLTheoremA.HSubT.guBlockFacts_holds hs3 hs1 hJ
  let S : Type := ↥J ⧸ Subgroup.center ↥J
  change GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel) S ∨
    GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) S ∨
    GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) S
  rcases hcat with ⟨i, hi, ⟨eJ⟩⟩
  rcases hi with hU4 | hSp6 | hA6cat
  · obtain ⟨eBridge⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_u4two
      (S := S) ⟨i, hU4, ⟨eJ⟩⟩
    exact Or.inr (Or.inl (ggHasLabel_of_mulEquiv eBridge.symm ggHasLabel_psp43))
  · obtain ⟨eBridge⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_sp6two
      (S := S) ⟨i, hSp6, ⟨eJ⟩⟩
    exact Or.inl (ggHasLabel_of_mulEquiv eBridge.symm ggHasLabel_sp62)
  · obtain ⟨eJ6⟩ := hA6 ⟨i, hA6cat, ⟨eJ⟩⟩
    have hZ6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ := by
      rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6))]
    let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6) :=
      (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center (alternatingGroup (Fin 6)))
        eJ6 (Subgroup.map_center_eq eJ6)).trans
        ((QuotientGroup.quotientMulEquivOfEq hZ6).trans QuotientGroup.quotientBot)
    exact Or.inr (Or.inr (CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_b2der eQ))

theorem card_ggAutomizer_alt6_sylow_three {K : Type} [Group K] [Finite K]
    (hK : IsAltTwoP 3 K) (E : Sylow 3 K) :
    Nat.card (ggAutomizer (⊤ : Subgroup K) (E : Subgroup K)) = 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Esub : Subgroup K := E
  have hEcard : Nat.card Esub = 3 ^ 2 :=
    sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hK E
  have hcomm : IsMulCommutative Esub :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      (sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hK E)
  have hEleC : Esub ≤ Subgroup.centralizer (Esub : Set K) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm
  have h3dvd : 3 ∣ Nat.card Esub := by rw [hEcard]; norm_num
  obtain ⟨⟨a, haE⟩, ha3⟩ := exists_prime_orderOf_dvd_card' (G := Esub) 3 h3dvd
  have ha3' : orderOf (a : K) = 3 := by
    simpa [Subgroup.orderOf_mk] using ha3
  let eA6 : K ≃* alternatingGroup (Fin 6) := Classical.choice hK
  have hC_le : Subgroup.centralizer (Esub : Set K) ≤ Subgroup.centralizer ({(a : K)} : Set K) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haE)
  have hCcard : Nat.card (Subgroup.centralizer (Esub : Set K)) = 9 := by
    apply le_antisymm ?_ ?_
    · exact (Nat.card_le_card_of_injective
        (fun x : ↥(Subgroup.centralizer (Esub : Set K)) =>
          (⟨x.1, hC_le x.2⟩ : ↥(Subgroup.centralizer ({(a : K)} : Set K))))
        (fun x y hxy => Subtype.ext (congrArg
          (fun z : ↥(Subgroup.centralizer ({(a : K)} : Set K)) => (z : K)) hxy))).trans
        (AltSix.card_centralizer_le_nine eA6 ha3')
    · calc 9 = Nat.card Esub := by rw [hEcard]; norm_num
        _ ≤ Nat.card ↥(Subgroup.centralizer (Esub : Set K)) :=
          Nat.card_le_card_of_injective
            (fun x : Esub => (⟨x.1, hEleC x.2⟩ : ↥(Subgroup.centralizer (Esub : Set K))))
            (fun x y hxy => Subtype.ext
              (congrArg (fun z : ↥(Subgroup.centralizer (Esub : Set K)) => (z : K)) hxy))
  have hNcard : Nat.card (Subgroup.normalizer (Esub : Set K)) = 36 := by
    simpa [Esub] using AltSix.card_normalizer hK E
  let f : ↥(Subgroup.normalizer (Esub : Set K)) →* MulAut Esub :=
    Esub.normalizerMonoidHom
  have hker : Nat.card ↥(f.ker) = 9 := by
    have hk : f.ker = (Subgroup.centralizer (Esub : Set K)).subgroupOf
        (Subgroup.normalizer (Esub : Set K)) := by
      simpa [f] using Subgroup.normalizerMonoidHom_ker (H := Esub)
    rw [hk]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer (Esub : Set K))).toEquiv).trans hCcard
  have hcard : Nat.card ↥(f.range) = 4 := by
    have hmul := TableB.card_range_mul_card_ker f
    rw [hker, hNcard] at hmul
    omega
  have hrange : f.range = ggAutomizer (⊤ : Subgroup K) Esub := by
    ext phi
    rw [mem_ggAutomizer_iff]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨(g : K), Subgroup.mem_top _, g.2, fun b => ?_⟩
      have h := congrArg (fun psi : MulAut Esub => ((psi b : Esub) : K)) hg
      simpa [f, Subgroup.normalizerMonoidHom_apply_apply_coe] using h.symm
    · rintro ⟨g, -, hgN, hg⟩
      refine ⟨⟨g, hgN⟩, ?_⟩
      ext b
      simpa [f, Subgroup.normalizerMonoidHom_apply_apply_coe] using (hg b).symm
  rw [← hrange]
  exact hcard

theorem all_inner_of_mulEquiv_statedProjSp {X K : Type} [Group X] [Field K] [Finite K]
    {r : ℕ} (e : X ≃* StatedProj (StatedSp r K)) (hr : 3 ≤ r) (hK : Nat.card K = 2) :
    ∀ ψ : MulAut X, ∃ x : X, ψ = MulAut.conj x := by
  intro ψ
  obtain ⟨g, hg⟩ := SpTwoThree.all_inner_statedProj hK (r := r) hr
    (MulAut.congr e ψ)
  refine ⟨e.symm g, ?_⟩
  calc ψ = MulAut.congr e.symm (MulAut.congr e ψ) := by
        ext l
        simp [MulAut.congr_apply]
    _ = MulAut.congr e.symm (MulAut.conj g) := by rw [hg]
    _ = MulAut.conj (e.symm g) :=
        CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e.symm g

theorem rank4_transport_component
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hLlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (htag : lab.tag = .B ∨ lab.tag = .C) (hn1 : lab.n = 1) (hrank4 : lab.rank = 4)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (s : StatedSp 4 (GaloisField 2 1)) (J' : Subgroup (StatedSp 4 (GaloisField 2 1))),
      s ^ 3 = 1 ∧ s ≠ 1 ∧
      CFSG.Open.IsComponentOf J' (Subgroup.centralizer ({s} : Set (StatedSp 4 (GaloisField 2 1)))) ∧
      Nonempty (↥J ≃* ↥J') := by
  classical
  subst hp3
  have hpre : LargeEvenStdSubPre 3 B x L D J := hH.1.2.2.1
  have hDJle : D ≤ B := hpre.1
  have hDcard : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hxDLE : x ∈ D := hpre.2.2.2.1
  let C : Subgroup G := L ⊓ Subgroup.centralizer (D : Set G)
  have hJcomp : CFSG.Assembly.IsComponentOf J C := hpre.2.2.2.2.2.1
  have hJleL : J ≤ L := le_of_stdSub_left hH.1.2.2
  have hJleC : J ≤ C := hJcomp.1
  have hDJ : D ≤ Subgroup.centralizer (J : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (hJleC hj).2 d hd).symm
  have hS : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hS.2.2.2.1.1 hl) x (by simp)).symm
  have hDxy : D = Subgroup.closure ({x, y} : Set G) := (hH.2.2.2.2.1).2.1
  have hyD : y ∈ D := by
    rw [hDxy]
    exact Subgroup.subset_closure (by simp)
  have hBle : B ≤ Bs := hH.1.2.1.1
  have hyBs : y ∈ Bs := hBle (hDJle hyD)
  let β : ↥Bs →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBsN)
  have hβapp : ∀ (b : ↥Bs) (l : ↥L), ((β b l : ↥L) : G) = (b : G) * (l : G) * (b : G)⁻¹ := by
    intro b l
    simp [β, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hZL : Subgroup.center ↥L = ⊥ :=
    CFSG.StandardType.HdRo7C.hdRo7CLOSpAux_center_L_eq_bot hH lab hlab hLlab htag hn1 (by omega)
  have hlabEq : (⟨lab.tag, 4, 1⟩ : LargeEvenLabel) = lab := by
    cases lab with
    | mk tag rank n =>
        subst hrank4
        subst hn1
        rfl
  have hLlab4 : GGHasLabel (⟨lab.tag, 4, 1⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L) := by
    rw [hlabEq]
    exact hLlab
  have hmodelQ : CFSG.Open.StatedClassicalModel
      (↥L ⧸ Subgroup.center ↥L) .PSp 4 2 1 :=
    CFSG.StandardType.HdRo7C.hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC (tag := lab.tag) htag (by norm_num : 3 ≤ 4)
      (by omega : 1 ≤ 1) hLlab4
  have hmodelL : CFSG.Open.StatedClassicalModel ↥L .PSp 4 2 1 := by
    obtain ⟨hadm, K, hF, hfin, hKcard, ⟨e⟩⟩ := hmodelQ
    refine ⟨hadm, K, hF, hfin, hKcard, ?_⟩
    let eLQ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot
    exact ⟨eLQ.symm.trans e⟩
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨eProj⟩⟩ := hmodelL
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have hAllInner : ∀ φ : MulAut ↥L, ∃ l : ↥L, φ = MulAut.conj l :=
    @all_inner_of_mulEquiv_statedProjSp ↥L K _ hKfield hKfin 4 eProj (by norm_num) hK2
  obtain ⟨Yh, hYh⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts2.exists_inner_hom (p := 3) (D := ↥Bs)
    (fun b => Subtype.ext (by
      simpa using (hH.1.2.1.2.1).2 b b.2))
    (MulEquiv.refl ↥L) β
    (fun σ _ => hAllInner σ)
    (fun z hz => by
      have hz' : z ∈ Subgroup.center ↥L := Subgroup.mem_center_iff.mpr (fun x => (hz x).symm)
      rw [hZL] at hz'
      exact Subgroup.mem_bot.mp hz')
  let s : ↥L := Yh ⟨y, hyBs⟩
  have hy3 : y ^ 3 = 1 := (hH.1.2.1.2.1).2 y hyBs
  have hs3 : s ^ 3 = 1 := by
    have hyB3 : (⟨y, hyBs⟩ : ↥Bs) ^ 3 = 1 := Subtype.ext hy3
    calc s ^ 3 = Yh ((⟨y, hyBs⟩ : ↥Bs) ^ 3) := by
          dsimp [s]
          exact (map_pow Yh _ 3).symm
      _ = Yh 1 := by rw [hyB3]
      _ = 1 := map_one Yh
  have hs1 : s ≠ 1 := by
    intro hs
    have hβy : β ⟨y, hyBs⟩ = 1 := by
      ext l
      have hone : (1 : MulAut ↥L) l = l := rfl
      rw [hone]
      have hG : ((β ⟨y, hyBs⟩ l : ↥L) : G) = (s : G) * (l : G) * (s : G)⁻¹ := by
        have h := congrArg (fun z : ↥L => (z : G)) (hYh ⟨y, hyBs⟩ l)
        simp only [MulEquiv.coe_refl, id_eq] at h
        simpa only [s, Subgroup.coe_mul, Subgroup.coe_inv] using h
      have hG' : ((β ⟨y, hyBs⟩ l : ↥L) : G) = (l : G) := by
        simpa [hs, Subgroup.coe_mul, Subgroup.coe_inv] using hG
      exact hG'
    have hyCent : y ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : G)) hβy
      have hβl : ((β ⟨y, hyBs⟩ ⟨l, hl⟩ : ↥L) : G) = (l : G) := by simpa using h
      have hconj : y * l * y⁻¹ = l := by
        simpa [β, Subgroup.normalizerMonoidHom_apply_apply_coe] using hβl
      have hycomm : y * l = l * y := by
        calc y * l = (y * l * y⁻¹) * y := by group
          _ = l * y := by rw [hconj]
      exact hycomm.symm
    have hxCent : x ∈ Subgroup.centralizer (L : Set G) := hxL
    have hDcent : D ≤ Subgroup.centralizer (L : Set G) := by
      rw [hDxy]
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact hxCent
      · exact hyCent
    have hcyc : IsCyclic ↥D :=
      hS.2.2.2.2 D hDcent (by
        exact (hpre.2.1.isElementaryAbelian).isPGroup)
    haveI : CFSG.IsElementaryAbelian 3 ↥D := hpre.2.1.isElementaryAbelian
    exact (CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq
      (p := 3) hDcard) hcyc
  have hCeq : C = L ⊓ Subgroup.centralizer ({(s : G)} : Set G) := by
    ext l
    constructor
    · rintro ⟨hlL, hlC⟩
      refine ⟨hlL, ?_⟩
      change ∀ z ∈ ({(s : G)} : Set G), z * l = l * z
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      have hycomm : y * l = l * y := (Subgroup.mem_centralizer_iff.mp hlC) y hyD
      have hconj : y * l * y⁻¹ = (s : G) * l * (s : G)⁻¹ := by
        calc y * l * y⁻¹ = ((β ⟨y, hyBs⟩ ⟨l, hlL⟩ : ↥L) : G) :=
              (hβapp ⟨y, hyBs⟩ ⟨l, hlL⟩).symm
          _ = (s : G) * l * (s : G)⁻¹ := by
              have h := congrArg (fun z : ↥L => (z : G)) (hYh ⟨y, hyBs⟩ ⟨l, hlL⟩)
              simpa only [MulEquiv.coe_refl, id_eq, s, Subgroup.coe_mul, Subgroup.coe_inv] using h
      calc (s : G) * l = ((s : G) * l * (s : G)⁻¹) * (s : G) := by group
        _ = (y * l * y⁻¹) * (s : G) := by rw [hconj]
        _ = (l * y * y⁻¹) * (s : G) := by rw [hycomm]
        _ = l * (s : G) := by group
    · rintro ⟨hlL, hlC⟩
      refine ⟨hlL, ?_⟩
      change ∀ d ∈ (D : Set G), d * l = l * d
      intro d hd
      rw [hDxy] at hd
      have hmem : ∀ z ∈ Subgroup.closure ({x, y} : Set G), z * l = l * z := by
        intro z hz
        refine Subgroup.closure_induction (p := fun z _ => z * l = l * z) ?_ ?_ ?_ ?_ hz
        · intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hzx | hzy
          · rw [hzx]
            exact (Subgroup.mem_centralizer_iff.mp hxL l hlL).symm
          · rw [hzy]
            have hscomm : (s : G) * l = l * (s : G) :=
              (Subgroup.mem_centralizer_iff.mp hlC) (s : G) (by simp)
            have hconj : y * l * y⁻¹ = (s : G) * l * (s : G)⁻¹ := by
              calc y * l * y⁻¹ = ((β ⟨y, hyBs⟩ ⟨l, hlL⟩ : ↥L) : G) :=
                    (hβapp ⟨y, hyBs⟩ ⟨l, hlL⟩).symm
                _ = (s : G) * l * (s : G)⁻¹ := by
                    have h := congrArg (fun z : ↥L => (z : G)) (hYh ⟨y, hyBs⟩ ⟨l, hlL⟩)
                    simpa only [MulEquiv.coe_refl, id_eq, s, Subgroup.coe_mul, Subgroup.coe_inv] using h
            have hsconj : (s : G) * l * (s : G)⁻¹ = l := by
              calc (s : G) * l * (s : G)⁻¹ = (l * (s : G)) * (s : G)⁻¹ := by rw [hscomm]
                _ = l := by group
            calc y * l = (y * l * y⁻¹) * y := by group
              _ = ((s : G) * l * (s : G)⁻¹) * y := by rw [hconj]
              _ = l * y := by rw [hsconj]
        · simp
        · intro a b hma hmb ha hb
          calc (a * b) * l = a * (b * l) := by group
            _ = a * (l * b) := by rw [hb]
            _ = (a * l) * b := by group
            _ = (l * a) * b := by rw [ha]
            _ = l * (a * b) := by group
        · intro a hma ha
          calc a⁻¹ * l = a⁻¹ * (l * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * l) * a⁻¹ := by rw [ha]
            _ = l * a⁻¹ := by group
      exact hmem d hd
  have hJcompL : CFSG.Open.IsComponentOf (J.subgroupOf L)
      (Subgroup.centralizer ({s} : Set ↥L)) := by
    have hJ' : CFSG.Assembly.IsComponentOf J C := hJcomp
    rw [hCeq] at hJ'
    have h1 : CFSG.Assembly.IsComponentOf (J.subgroupOf L)
        ((L ⊓ Subgroup.centralizer ({(s : G)} : Set G)).subgroupOf L) := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff L.subtype_injective]
      rw [Subgroup.map_subgroupOf_eq_of_le hJleL]
      rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left]
      exact hJ'
    have h2 : (L ⊓ Subgroup.centralizer ({(s : G)} : Set G)).subgroupOf L =
        Subgroup.centralizer ({s} : Set ↥L) := by
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left,
        CFSG.LocalAnalysis.ComponentInitial.map_subtype_centralizer_singleton]
    rw [h2] at h1
    exact (CFSG.Assembly.isComponentOf_iff_open).1 h1
  have hperf : commutator ↥L = ⊤ := hH.2.2.1.1.1
  obtain ⟨φ, hφinj, hφrange⟩ :=
    ggSpLiftInput_holds G L 4 1 (by norm_num) hperf hmodelQ
  let φL : StatedSp 4 (GaloisField 2 1) →* ↥L :=
    { toFun := fun a => ⟨φ a, by
        have ha : φ a ∈ φ.range := ⟨a, rfl⟩
        rwa [hφrange] at ha⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hφLinj : Function.Injective φL := by
    intro a b hab
    apply hφinj
    exact Subtype.ext_iff.mp hab
  have hφLsurj : Function.Surjective φL := by
    intro l
    have hl : (l : G) ∈ φ.range := by rw [hφrange]; exact l.2
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hl
    exact ⟨a, Subtype.ext ha⟩
  let eSp : StatedSp 4 (GaloisField 2 1) ≃* ↥L :=
    MulEquiv.ofBijective φL ⟨hφLinj, hφLsurj⟩
  let eL : ↥L ≃* StatedSp 4 (GaloisField 2 1) := eSp.symm
  let s' : StatedSp 4 (GaloisField 2 1) := eL s
  let J' : Subgroup (StatedSp 4 (GaloisField 2 1)) :=
    (J.subgroupOf L).map eL.toMonoidHom
  have hJ'comp : CFSG.Open.IsComponentOf J'
      (Subgroup.centralizer ({s'} : Set (StatedSp 4 (GaloisField 2 1)))) := by
    have hJ'' : CFSG.Assembly.IsComponentOf J'
        ((Subgroup.centralizer ({s} : Set ↥L)).map eL.toMonoidHom) := by
      exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
        (K := J.subgroupOf L) (C := Subgroup.centralizer ({s} : Set ↥L))
        ((CFSG.Assembly.isComponentOf_iff_open).2 hJcompL) eL.toMonoidHom eL.injective
    have hmap : (Subgroup.centralizer ({s} : Set ↥L)).map eL.toMonoidHom =
        Subgroup.centralizer ({s'} : Set (StatedSp 4 (GaloisField 2 1))) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv]
    rw [hmap] at hJ''
    exact (CFSG.Assembly.isComponentOf_iff_open).1 hJ''
  have hs'3 : s' ^ 3 = 1 := by
    dsimp [s']
    rw [← map_pow, hs3, map_one]
  have hs'1 : s' ≠ 1 := by
    intro h
    apply hs1
    have := congrArg eSp h
    simpa [s', eL] using this
  refine ⟨s', J', hs'3, hs'1, hJ'comp, ?_⟩
  refine ⟨(Subgroup.subgroupOfEquivOfLe hJleL).symm.trans ?_⟩
  exact Subgroup.equivMapOfInjective (J.subgroupOf L) eL.toMonoidHom eL.injective



theorem ggResSmallSpFour_component_labels
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L) :
    ∃ (s : StatedSp 4 (ZMod 2)) (J' : Subgroup (StatedSp 4 (ZMod 2))),
      s ^ 3 = 1 ∧ s ≠ 1 ∧
      CFSG.Open.IsComponentOf J' (Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2)))) ∧
      Nonempty (↥J ≃* ↥J') ∧
      (GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) ∨
        GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) ∨
        GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) := by
  classical
  obtain ⟨lab, hlab, hLlab, R, instR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hP.1.1
  have htag : lab.tag = .B ∨ lab.tag = .C := hP.1.2.1
  have hn1 : lab.n = 1 := hP.1.2.2.1
  have hrank4 : lab.rank = 4 := hP.1.2.2.2
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := hP.2.1
  subst hp3
  obtain ⟨s₀, J₀, hs₀3, hs₀1, hJ₀, eJ₀⟩ :=
    rank4_transport_component hH rfl lab hlab hLlab htag hn1 hrank4 hBsN
  let φ : GaloisField 2 1 ≃+* ZMod 2 := (GaloisField.equivZmodP (p := 2)).toRingEquiv
  let eSp : StatedSp 4 (GaloisField 2 1) ≃* StatedSp 4 (ZMod 2) :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr φ 4
  let s : StatedSp 4 (ZMod 2) := eSp s₀
  let J' : Subgroup (StatedSp 4 (ZMod 2)) := J₀.map eSp.toMonoidHom
  have hs3 : s ^ 3 = 1 := by
    dsimp [s]
    rw [← map_pow, hs₀3, map_one]
  have hs1 : s ≠ 1 := by
    intro h
    apply hs₀1
    have := congrArg eSp.symm h
    simpa [s, eSp] using this
  have hJ' : CFSG.Open.IsComponentOf J'
      (Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2)))) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
      (K := J₀) (C := Subgroup.centralizer ({s₀} : Set (StatedSp 4 (GaloisField 2 1))))
      ((CFSG.Assembly.isComponentOf_iff_open).2 hJ₀) eSp.toMonoidHom eSp.injective
    have hmap : (Subgroup.centralizer ({s₀} : Set (StatedSp 4 (GaloisField 2 1)))).map
        eSp.toMonoidHom = Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv]
    rw [hmap] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).1 h
  have hlabJ' := sp8_order_three_component_labels hs3 hs1 hJ'
  have eJ₀' : ↥J ≃* ↥J₀ := Classical.choice eJ₀
  have eJJ' : ↥J ≃* ↥J' := eJ₀'.trans (Subgroup.equivMapOfInjective J₀ eSp.toMonoidHom eSp.injective)
  have eQ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥J' ⧸ Subgroup.center ↥J') :=
    QuotientGroup.congr _ _ eJJ' (Subgroup.map_center_eq eJJ')
  refine ⟨s, J', hs3, hs1, hJ', ⟨eJJ'⟩, ?_⟩
  rcases hlabJ' with h | h | h
  · exact Or.inl (ggHasLabel_of_mulEquiv eQ.symm h)
  · exact Or.inr (Or.inl (ggHasLabel_of_mulEquiv eQ.symm h))
  · exact Or.inr (Or.inr (ggHasLabel_of_mulEquiv eQ.symm h))



theorem ggWeylTypeData_B4 :
    GGWeylTypeData 4 384 2 := by
  have hM : CFSG.StandardType.GGIsWeylMatrix (CoxeterMatrix.B 4) :=
    CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_B 4 (by norm_num)
  have hdata := CFSG.StandardType.ggWeylTypeData_of_isWeylMatrix hM
  simpa [Nat.card_eq_fintype_card, ggCoxeterB_card 4 (by norm_num),
    ggCoxeterB_center 4 (by norm_num), Nat.factorial] using hdata

theorem ggResSmallSpFour_exactTwo_rank_two
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hJ : ggAutomizer J Bs ≠ ⊥)
    (hAL : Nat.card ↥(ggAutomizer L Bs) = 384) :
    ∃ (Λ : Type) (_ : Fintype Λ), Fintype.card Λ = 4 ∧
      ∃ r : ℕ, r = 2 ∧ GGWeylTypeData r (Nat.card ↥(ggAutomizer J Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
  classical
  have h2keep := h2
  obtain ⟨Λ, hΛfin, hΛdec, S, Λa, hΛafin, hΛadec, ML, CL, MK, CK, V,
    hVadd, hVmod, ι, φ, h, α, hScard, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp,
    hlin, hrefl, hCLcart, hCKcart, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hgenL, hgenK,
    hdel, hgenJ⟩ := h2keep
  have hX : GGWeylTypeData 4 384 2 := ggWeylTypeData_B4
  have hX' : GGWeylTypeData 4 (Nat.card ↥(ggAutomizer L Bs)) 2 := by
    rw [← hAL] at hX
    exact hX
  have hMLdata := ggWeylTypeData_of_isWeylMatrix hML
  have hcardML : Nat.card ML.Group = 384 := by
    rw [Nat.card_congr fL.toEquiv, hAL]
  have hMLdata' : GGWeylTypeData (Fintype.card Λ) 384
      (Nat.card ↥(Subgroup.center ML.Group)) := by
    rwa [hcardML] at hMLdata
  have hcardΛ : Fintype.card Λ = 4 :=
    ggWeylTypeData_rank_eq hMLdata' hX
  obtain ⟨r, hr, hsurv⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData h2 hJ hX'
  have hr' : r = 2 := by omega
  exact ⟨Λ, hΛfin, hcardΛ, r, hr', hsurv⟩


lemma c4_aut_of_torus_data
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hCfg : GGConfig 3 B Bs x L D J)
    (hLperf : commutator ↥L = ⊤)
    (hZL : Subgroup.center ↥L = ⊥)
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹)
    {R : Type} [Group R] (I : Set (MulAut R))
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
      (fun l l' => (l' : G) = b⁻¹ * (l : G) * b) φ)
    (hSC : GGTorusAutCardSC 3 R I 4 384) :
    Nat.card ↥(ggAutomizer L Bs) = 384 := by
  classical
  have hAh : CFSG.Open.IsElemAbelian 3 (ggGamma L hBsN).range :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).1
  have hAI : ∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ I, ∀ l : ↥L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).2.1
  have h3A : 3 ^ 3 ≤ Nat.card ↥(ggGamma L hBsN).range :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).2.2.1
  have hscA : GGTorusSelfCent 3 (ggGamma L hBsN).range :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).2.2.2
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center ↥L := by
    intro q hq
    rw [MonoidHom.mem_ker] at hq
    have hq' : (QuotientGroup.mk' (Subgroup.center ↥L)) q = 1 := by
      apply θ.injective
      simpa [ψ] using hq
    exact (QuotientGroup.eq_one_iff q).mp hq'
  have hSCapp := hSC ↥L ψ hψsurj hψker hLperf (ggGamma L hBsN).range
    hAh hAI h3A hscA
  have hZL' : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
    intro g hg
    rw [hZL] at hg
    have hg1 : g = 1 := Subgroup.mem_bot.mp hg
    subst hg1
    simp
  have hcard1 : Nat.card ↥(ggAutomizer L Bs) =
      Nat.card ↥(ggAutomizer L (Bs ⊓ L)) :=
    (ggLemma47c hCfg.tableB_facts.2.1 hCfg.2.1.2.2.2 hZL' hInnL).2.2.2.2
  have hBsEA : CFSG.Open.IsElemAbelian 3 Bs := hCfg.tableB_facts.2.1
  have hBXea : CFSG.Open.IsElemAbelian 3 (Bs ⊓ L) := by
    constructor
    · refine ⟨⟨fun a b => ?_⟩⟩
      apply Subtype.ext
      exact CFSG.Open.IsElemAbelian.comm hBsEA
        (Subgroup.mem_inf.mp a.2).1 (Subgroup.mem_inf.mp b.2).1
    · intro a ha
      exact hBsEA.2 a (Subgroup.mem_inf.mp ha).1
  have hcard2 : Nat.card ↥(ggAutomizer L (Bs ⊓ L)) =
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
        (Subgroup.map MulAut.conj ((Bs ⊓ L).subgroupOf L))) :=
    ggAutomizer_card_eq_inn inf_le_right hBXea hZL'
  have hrange := range_ggGamma_eq_map hCfg hZL' hInnL hBsN
  calc Nat.card ↥(ggAutomizer L Bs)
      = Nat.card ↥(ggAutomizer L (Bs ⊓ L)) := hcard1
    _ = Nat.card ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
          (Subgroup.map MulAut.conj ((Bs ⊓ L).subgroupOf L))) := hcard2
    _ = Nat.card ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
          (ggGamma L hBsN).range) := by rw [← hrange]
    _ = 384 := hSCapp.2

theorem ggResC4_automizerL_card_eq_384
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hCfg : GGConfig 3 B Bs x L D J)
    (hC4 : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4)
      3 Bs L)
    (hLperf : commutator ↥L = ⊤)
    (hZL : Subgroup.center ↥L = ⊥)
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹) :
    Nat.card ↥(ggAutomizer L Bs) = 384 := by
  classical
  obtain ⟨-, lab, -, hraw⟩ := hC4
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R0, _, I0, F0, hsimple0, hna0, θ0, hP0⟩ :=
    CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨⟨-, htag, hn, hr⟩, hBsN0, hBs30⟩ := hP0
  subst hn
  subst hr
  rcases htag with rfl | rfl
  · obtain ⟨K, hField, hFinite, hKcard, hQ⟩ := hraw
    obtain ⟨hsimple, hna, θ, hP⟩ := hQ
    obtain ⟨-, hBsN, hBs3⟩ := hP
    letI := hField
    letI := hFinite
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hKcard
    have hSC : GGTorusAutCardSC 3
        (LargeEvenProj (LargeEvenSpGroup K 4))
        (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K 4)) 4 384 :=
      KGA.kga_sp (K := K) (N := 4) (p := 3) (by norm_num) Nat.prime_three (by norm_num)
        (by rw [hKcard]; norm_num)
    exact c4_aut_of_torus_data hCfg hLperf hZL hInnL _ θ hBsN hBs3 hSC
  · obtain ⟨K, hField, hFinite, hKcard, hQ⟩ := hraw
    obtain ⟨hsimple, hna, θ, hP⟩ := hQ
    obtain ⟨-, hBsN, hBs3⟩ := hP
    letI := hField
    letI := hFinite
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hKcard
    have hSC : GGTorusAutCardSC 3
        (LargeEvenProj (LargeEvenSpGroup K 4))
        (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K 4)) 4 384 :=
      KGA.kga_sp (K := K) (N := 4) (p := 3) (by norm_num) Nat.prime_three (by norm_num)
        (by rw [hKcard]; norm_num)
    exact c4_aut_of_torus_data hCfg hLperf hZL hInnL _ θ hBsN hBs3 hSC



theorem rank4_innerOnL
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (lab : LargeEvenLabel)
    (hlab : LargeEvenInLambda2 lab)
    (hLlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (htag : lab.tag = .B ∨ lab.tag = .C) (hn1 : lab.n = 1) (hrank4 : lab.rank = 4)
    (hp3 : p = 3) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ := by
  subst hp3
  have hS : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
  have hZL : Subgroup.center ↥L = ⊥ :=
    CFSG.StandardType.HdRo7C.hdRo7CLOSpAux_center_L_eq_bot hH lab hlab hLlab htag hn1 (by omega)
  have hlabEq : (⟨lab.tag, 4, 1⟩ : LargeEvenLabel) = lab := by
    cases lab with
    | mk tag rank n =>
        subst hrank4
        subst hn1
        rfl
  have hLlab4 : GGHasLabel (⟨lab.tag, 4, 1⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L) := by
    rw [hlabEq]
    exact hLlab
  have hmodelQ : CFSG.Open.StatedClassicalModel
      (↥L ⧸ Subgroup.center ↥L) .PSp 4 2 1 :=
    CFSG.StandardType.HdRo7C.hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC
      (tag := lab.tag) htag (by norm_num : 3 ≤ 4) (by omega : 1 ≤ 1) hLlab4
  have hmodelL : CFSG.Open.StatedClassicalModel ↥L .PSp 4 2 1 := by
    obtain ⟨hadm, K, hF, hfin, hKcard, ⟨e⟩⟩ := hmodelQ
    refine ⟨hadm, K, hF, hfin, hKcard, ?_⟩
    let eLQ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot
    exact ⟨eLQ.symm.trans e⟩
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨eProj⟩⟩ := hmodelL
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have hAllInner : ∀ φ : MulAut ↥L, ∃ l : ↥L, φ = MulAut.conj l :=
    @all_inner_of_mulEquiv_statedProjSp ↥L K _ hKfield hKfin 4 eProj (by norm_num) hK2
  let β : ↥Bs →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBsN)
  have hβapp : ∀ (b : ↥Bs) (l : ↥L), ((β b l : ↥L) : G) = (b : G) * (l : G) * (b : G)⁻¹ := by
    intro b l
    simp [β, Subgroup.normalizerMonoidHom_apply_apply_coe]
  obtain ⟨Yh, hYh⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts2.exists_inner_hom
    (p := 3) (D := ↥Bs)
    (fun b => Subtype.ext (by simpa using (hH.1.2.1.2.1).2 b b.2))
    (MulEquiv.refl ↥L) β (fun σ _ => hAllInner σ)
    (fun z hz => by
      have hz' : z ∈ Subgroup.center ↥L := Subgroup.mem_center_iff.mpr (fun x => (hz x).symm)
      rw [hZL] at hz'
      exact Subgroup.mem_bot.mp hz')
  intro b hb
  refine ⟨Yh ⟨b, hb⟩, (Yh ⟨b, hb⟩).2, ?_⟩
  intro l hl
  have h1 := hβapp ⟨b, hb⟩ ⟨l, hl⟩
  have h2 := congrArg (fun z : ↥L => (z : G)) (hYh ⟨b, hb⟩ ⟨l, hl⟩)
  exact h1.symm.trans h2

theorem ggResSmallSpFour_automizerL_card
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L) :
    Nat.card ↥(ggAutomizer L Bs) = 384 := by
  obtain ⟨lab, hlab, hLlab, R, instR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hP.1.1
  have htag : lab.tag = .B ∨ lab.tag = .C := hP.1.2.1
  have hn1 : lab.n = 1 := hP.1.2.2.1
  have hrank4 : lab.rank = 4 := hP.1.2.2.2
  subst hp3
  have hLperf : commutator ↥L = ⊤ := hH.2.2.1.1.1
  have hZL : Subgroup.center ↥L = ⊥ :=
    CFSG.StandardType.HdRo7C.hdRo7CLOSpAux_center_L_eq_bot hH lab hlab hLlab htag hn1 (by omega)
  have hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ :=
    rank4_innerOnL hH lab hlab hLlab htag hn1 hrank4 rfl hP.2.1
  exact ggResC4_automizerL_card_eq_384 hH.1 hM hLperf hZL hInnL


lemma ggWeylTypeData_two_four_false (c : ℕ) : ¬ GGWeylTypeData 2 4 c := by
  intro h
  rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
  all_goals norm_num at h

theorem ggResSmallSpFour_A6_exactTwo_false_of_card_four
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hJ : ggAutomizer J Bs ≠ ⊥)
    (hAJ4 : Nat.card ↥(ggAutomizer J Bs) = 4) :
    False := by
  have hAL : Nat.card ↥(ggAutomizer L Bs) = 384 :=
    ggResSmallSpFour_automizerL_card hH hM
  obtain ⟨Λ, hΛ, hcard, r, hr, hW⟩ :=
    ggResSmallSpFour_exactTwo_rank_two h2 hJ hAL
  subst hr
  have h4 : GGWeylTypeData 2 4
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa [hAJ4] using hW
  exact ggWeylTypeData_two_four_false _ h4


lemma ggWeylTypeData_two_dvd_four_false {n c : ℕ} (h : GGWeylTypeData 2 n c)
    (hdvd : n ∣ 4) : False := by
  rcases h with ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
    ⟨-, hn, -⟩
  · rw [hn] at hdvd
    norm_num at hdvd
  · rw [hn] at hdvd
    norm_num at hdvd
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · rw [hn] at hdvd
    norm_num at hdvd

theorem ggResSmallSpFour_A6_exactTwo_false_of_dvd_four
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hJ : ggAutomizer J Bs ≠ ⊥)
    (hAJdvd : Nat.card ↥(ggAutomizer J Bs) ∣ 4) :
    False := by
  have hAL : Nat.card ↥(ggAutomizer L Bs) = 384 :=
    ggResSmallSpFour_automizerL_card hH hM
  obtain ⟨Λ, hΛ, hcard, r, hr, hW⟩ :=
    ggResSmallSpFour_exactTwo_rank_two h2 hJ hAL
  subst hr
  exact ggWeylTypeData_two_dvd_four_false hW hAJdvd

theorem card_ggAutomizer_alt6_threeSubgroup_le_four
    {K : Type} [Group K] [Finite K] (hK : IsAltTwoP 3 K) (E : Subgroup K)
    (hE3 : IsPGroup 3 E) :
    Nat.card ↥(ggAutomizer (⊤ : Subgroup K) E) ≤ 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eA6⟩ := hK
  have hKcard : Nat.card K = 360 := by
    have h : Nat.card K = Nat.card (alternatingGroup (Fin 6)) := by
      simpa using Nat.card_congr eA6.toEquiv
    rw [h, nat_card_alternatingGroup]
    norm_num
  obtain ⟨k, hk⟩ := hE3.exists_card_eq
  have hdvd : Nat.card E ∣ Nat.card K := Subgroup.card_subgroup_dvd_card E
  have h27 : ¬ (27 : ℕ) ∣ Nat.card E := by
    intro h
    have h' : (27 : ℕ) ∣ Nat.card K := h.trans hdvd
    rw [hKcard] at h'
    norm_num at h'
  have hk2 : k ≤ 2 := by
    by_contra h
    have h3 : (3 : ℕ) ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    rw [← hk] at h3
    exact h27 (by norm_num at h3 ⊢; exact h3)
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · have hE1 : Nat.card E = 1 := by simpa using hk
    have hbot : E = ⊥ := E.card_le_one_iff_eq_bot.mp (by omega)
    subst hbot
    have hsub : Subsingleton ↥(ggAutomizer (⊤ : Subgroup K) (⊥ : Subgroup K)) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (a : MulAut ↥(⊥ : Subgroup K))
        (b : MulAut ↥(⊥ : Subgroup K)))⟩
    have hinj : Function.Injective
        (fun _ : ↥(ggAutomizer (⊤ : Subgroup K) (⊥ : Subgroup K)) => ()) :=
      fun a b _ => Subsingleton.elim a b
    have hle1 := Nat.card_le_card_of_injective
      (fun _ : ↥(ggAutomizer (⊤ : Subgroup K) (⊥ : Subgroup K)) => ()) hinj
    have hUnit : Nat.card Unit = 1 := by simp
    omega
  · have hE3card : Nat.card E = 3 := by simpa using hk
    haveI : IsCyclic ↥E := isCyclic_of_prime_card hE3card
    have hAut : Nat.card (MulAut ↥E) = 2 := by
      rw [IsCyclic.card_mulAut, hE3card]
      exact Nat.totient_prime Nat.prime_three
    have hle : Nat.card ↥(ggAutomizer (⊤ : Subgroup K) E) ≤ Nat.card (MulAut ↥E) :=
      Nat.le_of_dvd (Nat.card_pos)
        (Subgroup.card_subgroup_dvd_card (ggAutomizer (⊤ : Subgroup K) E))
    omega
  · have hE9 : Nat.card E = 9 := by simpa using hk
    have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
    have hidx : E.index = 40 := by
      have h := E.card_mul_index
      rw [hE9, hKcard] at h
      omega
    let P : Sylow 3 K := hEp.toSylow (by rw [hidx]; norm_num)
    have hPcoe : (P : Subgroup K) = E := IsPGroup.toSylow_coe hEp _
    have hcardP := card_ggAutomizer_alt6_sylow_three ⟨eA6⟩ P
    rw [hPcoe] at hcardP
    omega


lemma six_le_card_of_weylTypeData_two {n c : ℕ} (h : GGWeylTypeData 2 n c) : 6 ≤ n := by
  rcases h with ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
    ⟨-, hn, -⟩
  · rw [hn]
    norm_num
  · rw [hn]
    norm_num
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · rw [hn]
    norm_num

theorem GGResHyp.card_automizer_J_eq_four_of_A6
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hA6 : Nonempty (↥J ≃* alternatingGroup (Fin 6))) :
    Nat.card ↥(ggAutomizer J Bs) = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  obtain ⟨eJ6⟩ := hA6
  have hZ6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ := by
    rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6))]
  have hZJ : Subgroup.center ↥J = ⊥ := by
    have hmap := Subgroup.map_center_eq eJ6
    rw [hZ6] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (f := eJ6.toMonoidHom)
      (H := Subgroup.center ↥J) eJ6.injective).1 hmap
  have hBs3 : ∀ b ∈ Bs, b ^ 3 = 1 := hH.1.2.1.2.1.2
  have hinner : ∀ b ∈ Bs, ∃ j ∈ J, ∀ xx ∈ J, b * xx * b⁻¹ = j * xx * j⁻¹ := by
    intro b hb
    let φ : MulAut ↥J :=
      (Subgroup.normalizerMonoidHom J) ⟨b, hH.Bs_le_normalizer_J hb⟩
    have hφ3 : φ ^ 3 = 1 := by
      ext xx
      change b * (b * (b * (xx : G) * b⁻¹) * b⁻¹) * b⁻¹ = (xx : G)
      calc b * (b * (b * (xx : G) * b⁻¹) * b⁻¹) * b⁻¹
          = (b * b * b) * (xx : G) * (b * b * b)⁻¹ := by group
        _ = (xx : G) := by
            rw [show b * b * b = 1 by
              calc b * b * b = b ^ 3 := by rw [pow_three, mul_assoc]
                _ = 1 := hBs3 b hb]
            group
    let φA : MulAut (alternatingGroup (Fin 6)) := MulAut.congr eJ6 φ
    have hφA3 : φA ^ 3 = 1 := by
      rw [← map_pow, hφ3, map_one]
    obtain ⟨gA, hgA⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.alt_three_aut_inner
        (by norm_num : 5 ≤ 6) φA hφA3
    refine ⟨eJ6.symm gA, (eJ6.symm gA).2, ?_⟩
    intro xx hxx
    have hφeq : φ = MulAut.conj (eJ6.symm gA) := by
      calc φ = MulAut.congr eJ6.symm (MulAut.congr eJ6 φ) := by
            ext y
            simp
        _ = MulAut.congr eJ6.symm (MulAut.conj gA) := by
            rw [show MulAut.congr eJ6 φ = MulAut.conj gA from hgA]
        _ = MulAut.conj (eJ6.symm gA) :=
            CFSG.ComponentClassification.OuterAutomorphisms.congr_conj eJ6.symm gA
    have h1 := congrArg (fun ψ : MulAut ↥J => (((ψ ⟨xx, hxx⟩ : ↥J) : G))) hφeq
    have h2 : (((φ ⟨xx, hxx⟩ : ↥J) : G)) = b * (xx : G) * b⁻¹ := by
      simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact h2.symm.trans (by simpa [MulAut.conj_apply] using h1)
  have hBs : GGBstar 3 B Bs := hH.1.2.1
  have h9gamma : 9 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range := by
    have h := GGResHyp.sq_le_card_gamma_J (p := 3) hH
    simpa using h
  let E : Subgroup G := Bs ⊓ J
  have hE_le_Bs : E ≤ Bs := inf_le_left
  have hE_le_J : E ≤ J := inf_le_right
  have hEabel : IsElemAbelian 3 E := IsElemAbelian.mono hBs.2.1 hE_le_Bs
  let γE : ↥E →* MulAut ↥J :=
    (ggGamma J hH.Bs_le_normalizer_J).comp (Subgroup.inclusion hE_le_Bs)
  have hγEker : γE.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hzC : ((z : ↥E) : G) ∈ Subgroup.centralizer (J : Set G) := by
      exact (ggGamma_eq_one_iff J hH.Bs_le_normalizer_J (Subgroup.inclusion hE_le_Bs z)).mp
        (by simpa [γE] using hz)
    have hzJ : ((z : ↥E) : G) ∈ J := z.2.2
    have hzcenter : (⟨((z : ↥E) : G), hzJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
    rw [hZJ, Subgroup.mem_bot] at hzcenter
    have hzval : ((⟨((z : ↥E) : G), hzJ⟩ : ↥J) : G) = (1 : G) :=
      congrArg (fun w : ↥J => (w : G)) hzcenter
    exact Subtype.ext hzval
  have hγErange : γE.range = (ggGamma J hH.Bs_le_normalizer_J).range := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      exact ⟨⟨(z : G), hE_le_Bs z.2⟩, rfl⟩
    · rintro _ ⟨b, rfl⟩
      obtain ⟨g, hgE, huC⟩ := B48Om.exists_mem_inf_mul hBs hZJ hinner b b.2
      let u : G := (g : G)⁻¹ * (b : G)
      have huBs : u ∈ Bs := Bs.mul_mem (Bs.inv_mem hgE.1) b.2
      have huU : u ∈ Bs ⊓ Subgroup.centralizer (J : Set G) :=
        ⟨huBs, by simpa [u] using huC⟩
      have hb_eq : (b : G) = (g : G) * u := by dsimp [u]; group
      refine ⟨⟨g, hgE⟩, ?_⟩
      have hgu : (⟨(b : G), b.2⟩ : ↥Bs) =
          ⟨g, hgE.1⟩ * ⟨u, huBs⟩ := by
        apply Subtype.ext
        exact hb_eq
      change γE ⟨g, hgE⟩ = (ggGamma J hH.Bs_le_normalizer_J) (⟨(b : G), b.2⟩ : ↥Bs)
      rw [hgu, map_mul]
      have hug : ggGamma J hH.Bs_le_normalizer_J ⟨u, huBs⟩ = 1 :=
        (ggGamma_eq_one_iff J hH.Bs_le_normalizer_J ⟨u, huBs⟩).mpr huU.2
      rw [hug, mul_one]
      rfl
  have hcardE : Nat.card E = Nat.card (ggGamma J hH.Bs_le_normalizer_J).range := by
    have hγE_inj : Function.Injective γE := (MonoidHom.ker_eq_bot_iff γE).mp hγEker
    let eγ : ↥E ≃ ↥γE.range :=
      Equiv.ofBijective (fun z : ↥E => (⟨γE z, ⟨z, rfl⟩⟩ : ↥γE.range)) (by
        constructor
        · intro a b h
          exact hγE_inj (Subtype.ext_iff.mp h)
        · rintro ⟨w, hw⟩
          obtain ⟨z, rfl⟩ := hw
          exact ⟨z, rfl⟩)
    have hcard : Nat.card E = Nat.card γE.range := Nat.card_congr eγ
    rwa [hγErange] at hcard
  have h9E : 9 ≤ Nat.card E := by
    rw [hcardE]
    exact h9gamma
  have hJcard : Nat.card ↥J = 360 := by
    have h : Nat.card ↥J = Nat.card (alternatingGroup (Fin 6)) := by
      simpa using Nat.card_congr eJ6.toEquiv
    rw [h, nat_card_alternatingGroup]
    norm_num
  have hE3p : IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup hEabel
  have hEcard9 : Nat.card E = 9 := by
    refine le_antisymm ?_ h9E
    obtain ⟨k, hk⟩ := hE3p.exists_card_eq
    have hdvd : Nat.card E ∣ Nat.card ↥J := Subgroup.card_dvd_of_le hE_le_J
    rw [hJcard] at hdvd
    have hk2 : k ≤ 2 := by
      by_contra h
      have h27E : (3 : ℕ) ^ 3 ∣ Nat.card E := by
        rw [hk]
        exact pow_dvd_pow 3 (by omega)
      have h27J : (3 : ℕ) ^ 3 ∣ 360 := h27E.trans hdvd
      norm_num at h27J
    calc Nat.card E = 3 ^ k := hk
      _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  let EJ : Subgroup ↥J := E.subgroupOf J
  have hcardEJ : Nat.card ↥EJ = 9 := by
    dsimp [EJ]
    rw [← hEcard9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_J).toEquiv
  have hEJp : IsPGroup 3 EJ := by
    apply IsPGroup.of_card (n := 2)
    rw [hcardEJ]
    norm_num
  have hidx : EJ.index = 40 := by
    have h := EJ.card_mul_index
    rw [hcardEJ, hJcard] at h
    omega
  let P : Sylow 3 ↥J := hEJp.toSylow (by rw [hidx]; norm_num)
  have hPcoe : (P : Subgroup ↥J) = EJ := IsPGroup.toSylow_coe hEJp _
  have hAJ4 : Nat.card ↥(ggAutomizer J Bs) = 4 := by
    have hcard_eq : Nat.card ↥(ggAutomizer J Bs) =
        Nat.card ↥(ggAutomizer J (Bs ⊓ J)) :=
      B48Om.ggAutomizer_card_eq hBs hZJ hinner
    have hEJmap : EJ.map J.subtype = Bs ⊓ J := by
      dsimp [EJ, E]
      rw [Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
    have hmap := F4AutWeyl.ggAutomizer_map_eq (f := J.subtype) J.subtype_injective
      (⊤ : Subgroup ↥J) EJ (B' := Bs ⊓ J) hEJmap
    have hleft : (⊤ : Subgroup ↥J).map J.subtype = J := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hmap' : ggAutomizer J (Bs ⊓ J) =
        (ggAutomizer (⊤ : Subgroup ↥J) EJ).map
          (MulAut.congr ((EJ.equivMapOfInjective J.subtype J.subtype_injective).trans
            (MulEquiv.subgroupCongr hEJmap))).toMonoidHom := by
      simpa [hleft, hEJmap] using hmap
    have hcard_transfer : Nat.card ↥(ggAutomizer J (Bs ⊓ J)) =
        Nat.card ↥(ggAutomizer (⊤ : Subgroup ↥J) EJ) := by
      rw [hmap']
      exact Subgroup.card_map_of_injective (MulAut.congr _).injective
    have hP4 := card_ggAutomizer_alt6_sylow_three ⟨eJ6⟩ P
    rw [hPcoe] at hP4
    rw [hcard_eq, hcard_transfer]
    exact hP4
  exact hAJ4

theorem ggResSmallSpFour_A6_false_of_iso
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hA6 : Nonempty (↥J ≃* alternatingGroup (Fin 6))) :
    False := by
  classical
  obtain ⟨lab, hlab, hLlab, R, instR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hP.1.1
  subst hp3
  have hAJ4 := hH.card_automizer_J_eq_four_of_A6 hA6
  have hAL : Nat.card ↥(ggAutomizer L Bs) = 384 :=
    ggResSmallSpFour_automizerL_card hH hM
  have hX : ∃ c, GGWeylTypeData 4 (Nat.card ↥(ggAutomizer L Bs)) c := by
    refine ⟨2, ?_⟩
    rw [hAL]
    exact ggWeylTypeData_B4
  have hJ := (ggResLeviDatumCard_survivor_dvd_and_ne h2 hX
    (by norm_num : 2 < 4) hH.Bs_le_normalizer_J (by norm_num : 3 ≠ 2)
    hH.1.2.1.2.1.2).2
  exact ggResSmallSpFour_A6_exactTwo_false_of_card_four hH hM h2 hJ hAJ4


theorem nonempty_alt6_of_B2der_transport
    {G : Type} [Group G] [Finite G]
    {s : StatedSp 4 (ZMod 2)} {J' : Subgroup (StatedSp 4 (ZMod 2))}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hcomp : CFSG.Open.IsComponentOf J' (Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2)))))
    {J : Subgroup G} (eJ : ↥J ≃* ↥J')
    (hB2 : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J)) :
    Nonempty (↥J ≃* alternatingGroup (Fin 6)) := by
  let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥J' ⧸ Subgroup.center ↥J') :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J') eJ
      (Subgroup.map_center_eq eJ)
  have hB2' : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
      (↥J' ⧸ Subgroup.center ↥J') :=
    ggHasLabel_of_mulEquiv eQ hB2
  obtain ⟨eQ6⟩ := ggB2der_label_iso_A6 hB2'
  obtain ⟨-, hA6cat⟩ := CFSG.LocalAnalysis.GLTheoremA.HSubT.sp8_comp
    CFSG.LocalAnalysis.GLTheoremA.HSubT.guBlockFacts_holds hs3 hs1 hcomp
  obtain ⟨eJ'6⟩ := hA6cat (CFSG.LocalAnalysis.GLTheoremA.HSubT.catalogIs_alt6_of_equiv eQ6)
  exact ⟨eJ.trans eJ'6⟩


theorem ggResSmallSpFour_B2der_false
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hB2 : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J)) :
    False := by
  obtain ⟨s, J', hs3, hs1, hcomp, ⟨eJ⟩, -⟩ :=
    ggResSmallSpFour_component_labels hH hM
  exact ggResSmallSpFour_A6_false_of_iso hH hM h2
    (nonempty_alt6_of_B2der_transport hs3 hs1 hcomp eJ hB2)


theorem ggResSmallSpFour_rank_three_false
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hW3 : GGWeylTypeData 3 (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs)))) :
    False := by
  have hAL : Nat.card ↥(ggAutomizer L Bs) = 384 :=
    ggResSmallSpFour_automizerL_card hH hM
  obtain ⟨lab, hlab, hLlab, R, instR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hP.1.1
  subst hp3
  have hX : ∃ c, GGWeylTypeData 4 (Nat.card ↥(ggAutomizer L Bs)) c := by
    refine ⟨2, ?_⟩
    rw [hAL]
    exact ggWeylTypeData_B4
  have hJ := (ggResLeviDatumCard_survivor_dvd_and_ne h2 hX
    (by norm_num : 2 < 4) hH.Bs_le_normalizer_J (by norm_num : 3 ≠ 2)
    hH.1.2.1.2.1.2).2
  obtain ⟨Λ, hΛ, hcardΛ, r, hr, hW2⟩ :=
    ggResSmallSpFour_exactTwo_rank_two h2 hJ hAL
  subst hr
  have hrank := ggWeylTypeData_rank_eq hW3 hW2
  omega


theorem ggResSmallSpFour_exactTwo_C3_or_twA
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) ∨
      GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨s, J', hs3, hs1, hcomp, eJ, hlabel⟩ :=
    ggResSmallSpFour_component_labels hH hM
  rcases hlabel with hC3 | htwA | hB2
  · exact Or.inl hC3
  · exact Or.inr htwA
  · exact (ggResSmallSpFour_B2der_false hH hM h2 hB2).elim

open CFSG.Open TableB

private theorem ggResSmallSpFour_J_statedClassicalModel_C31 {X : Type} [Group X]
    (hX : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel) X) :
    StatedClassicalModel X .PSp 3 2 1 := by
  unfold GGHasLabel at hX
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hX
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  have hmod : StatedClassicalModel (LargeEvenProj (LargeEvenSpGroup K 3)) .PSp 3 2 1 :=
    statedClassicalModel_symplectic 3 1 hK
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmod

private theorem ggResSmallSpFour_J_statedClassicalModel_twA31 {X : Type} [Group X]
    (hX : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) X) :
    StatedClassicalModel X .PSp 2 3 1 := by
  unfold GGHasLabel at hX
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hX
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  have hmod : StatedClassicalModel (LargeEvenProj (LargeEvenSUGroup (Fin 4) K 2)) .PSU 4 2 1 :=
    statedClassicalModel_unitary (K := K) 4 1 (by simpa using hK)
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩
  exact CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmod)

private theorem ggResSmallSpFour_J_innerAut_of_hasLabel {R : Type} [Group R]
    (h : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel) R ∨
      GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) R)
    {φ : MulAut R} (hφ3 : φ ^ 3 = 1) :
    ∃ r : R, φ = MulAut.conj r := by
  rcases h with h | h
  · exact CFSG.RankThree.PartTwo.Sec8.Hering611.exists_conj_eq_of_sp62
      (ggResSmallSpFour_J_statedClassicalModel_C31 h) φ
  · have hmem := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs196.mem_innerAut_of_psp43
      (ggResSmallSpFour_J_statedClassicalModel_twA31 h) hφ3
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, hr.symm⟩

private theorem ggResSmallSpFour_J_induces_cube_eq_one
    {G : Type} [Group G] {J : Subgroup G} {R : Type} [Group R]
    {Bs : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    {θ : ↥J ⧸ Subgroup.center ↥J ≃* R} {b : G} (hb : b ∈ Bs) (hb3 : b ^ 3 = 1)
    {φ : MulAut R}
    (h : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * (l : G) * b) φ) :
    φ ^ 3 = 1 := by
  have hmem : ∀ l : ↥J, b⁻¹ * (l : G) * b ∈ J := by
    intro l
    have hbN : b⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
      Subgroup.inv_mem _ (hN hb)
    have := (Subgroup.mem_normalizer_iff.mp hbN (l : G)).mp l.2
    simpa using this
  let cJ : ↥J → ↥J := fun l => ⟨b⁻¹ * (l : G) * b, hmem l⟩
  have hcJ : ∀ l : ↥J, ((cJ l : ↥J) : G) = b⁻¹ * (l : G) * b := fun l => rfl
  have hstep : ∀ l : ↥J, φ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (cJ l)) :=
    fun l => h l (cJ l) (hcJ l)
  have hb3' : b⁻¹ * b⁻¹ * b⁻¹ = 1 := by
    have h' : (b⁻¹) ^ 3 = 1 := by rw [inv_pow, hb3, inv_one]
    simpa [pow_succ, mul_assoc] using h'
  have hb3'' : b * b * b = 1 := by simpa [pow_succ, mul_assoc] using hb3
  have hcJ3 : ∀ l : ↥J, cJ (cJ (cJ l)) = l := by
    intro l
    apply Subtype.ext
    change b⁻¹ * (b⁻¹ * (b⁻¹ * (l : G) * b) * b) * b = (l : G)
    calc b⁻¹ * (b⁻¹ * (b⁻¹ * (l : G) * b) * b) * b
        = (b⁻¹ * b⁻¹ * b⁻¹) * (l : G) * (b * b * b) := by group
      _ = 1 * (l : G) * 1 := by rw [hb3', hb3'']
      _ = (l : G) := by simp
  have h3 : (φ ^ 3) = φ * φ * φ := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
  ext y
  obtain ⟨q, rfl⟩ := θ.surjective y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  rw [h3, MulAut.mul_apply, MulAut.mul_apply, hstep l, hstep (cJ l), hstep (cJ (cJ l)),
    hcJ3 l]
  rfl

private theorem ggResSmallSpFour_J_innerOn_of_marking
    {G : Type} [Group G] {J : Subgroup G} {R : Type} [Group R]
    {Bs : Subgroup G} {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hperf : commutator ↥J = ⊤)
    (hBs3 : ∀ b ∈ Bs, b ^ 3 = 1)
    {θ : ↥J ⧸ Subgroup.center ↥J ≃* R}
    (hind : ∀ b ∈ Bs,
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * (l : G) * b) φ)
    (hInner : ∀ φ ∈ I, φ ^ 3 = 1 → ∃ r : R, φ = MulAut.conj r) :
    ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹ := by
  intro b hb
  obtain ⟨φ, hφI, hφ⟩ := hind b hb
  have hφ3 : φ ^ 3 = 1 := ggResSmallSpFour_J_induces_cube_eq_one hN hb (hBs3 b hb) hφ
  obtain ⟨r, hr⟩ := hInner φ hφI hφ3
  obtain ⟨q, hq⟩ := θ.surjective r
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hbN : b⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
    Subgroup.inv_mem _ (hN hb)
  let α : MulAut ↥J := J.normalizerMonoidHom ⟨b⁻¹, hbN⟩
  have hαcoe : ∀ l : ↥J, ((α l : ↥J) : G) = b⁻¹ * (l : G) * b := by
    intro l
    change ((J.normalizerMonoidHom ⟨b⁻¹, hbN⟩ l : ↥J) : G) = b⁻¹ * (l : G) * b
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hquot : ∀ l : ↥J,
      (QuotientGroup.mk (α l) : ↥J ⧸ Subgroup.center ↥J) =
        QuotientGroup.mk ((MulAut.conj k) l) := by
    intro l
    apply θ.injective
    have h1 : θ (QuotientGroup.mk (α l)) = φ (θ (QuotientGroup.mk l)) :=
      (hφ l (α l) (hαcoe l)).symm
    have h2 : θ (QuotientGroup.mk ((MulAut.conj k) l)) = φ (θ (QuotientGroup.mk l)) := by
      rw [hr, MulAut.conj_apply, MulAut.conj_apply]
      rw [show QuotientGroup.mk (k * l * k⁻¹) =
          QuotientGroup.mk k * QuotientGroup.mk l * (QuotientGroup.mk k)⁻¹ by simp]
      rw [map_mul, map_mul, map_inv, hq]
    rw [h1, h2]
  have heq : α = MulAut.conj k :=
    CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.t2_perfect_aut_eq_of_mk_eq hperf α
      (MulAut.conj k) hquot
  have hcoeAll : ∀ x : ↥J, b⁻¹ * (x : G) * b = (k : G) * (x : G) * (k : G)⁻¹ := by
    intro x
    have h := congrArg (fun f : MulAut ↥J => ((f x : ↥J) : G)) heq
    simpa [α, MulAut.conj_apply] using h
  refine ⟨k⁻¹, J.inv_mem k.2, ?_⟩
  intro l hl
  have hbJl : b * l * b⁻¹ ∈ J := by
    exact (Subgroup.mem_normalizer_iff.mp (hN hb) l).mp hl
  have hcoe' : b⁻¹ * (b * l * b⁻¹) * b =
      (k : G) * (b * l * b⁻¹) * (k : G)⁻¹ := by
    have h := hcoeAll ⟨b * l * b⁻¹, hbJl⟩
    simpa using h
  have hmain : b * l * b⁻¹ = (k : G)⁻¹ * l * (k : G) := by
    have h1 : l = (k : G) * (b * l * b⁻¹) * (k : G)⁻¹ := by
      rw [← hcoe']; group
    calc b * l * b⁻¹
        = (k : G)⁻¹ * ((k : G) * (b * l * b⁻¹) * (k : G)⁻¹) * (k : G) := by group
      _ = (k : G)⁻¹ * l * (k : G) := by rw [← h1]
  simpa using hmain

theorem ggResSmallSpFour_J_innerOn
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (hLabel : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) ∨
      GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹ := by
  obtain ⟨labM, hlabM, hLlabM, RM, instRM, IM, FM, θM, hPM⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hPM.1.1
  subst hp3
  have hMbc : LargeEvenMarking L (fun lab _ _ I _ θ =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * (l : G) * b) φ) :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1.2.1, hP.2⟩) hM
  have hJOn : GGInnerDiagOn Bs J :=
    q1On_bc G 3 B Bs x L D J hH.1 hMbc
  obtain ⟨labJ, hlabJ, hlabelJ, R, instR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hJOn
  have hRlabel : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel) R ∨
      GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) R := by
    rcases hLabel with h | h
    · exact Or.inl (ggHasLabel_of_mulEquiv θ h)
    · exact Or.inr (ggHasLabel_of_mulEquiv θ h)
  have hInner : ∀ φ ∈ I, φ ^ 3 = 1 → ∃ r : R, φ = MulAut.conj r :=
    fun φ _ hφ3 => ggResSmallSpFour_J_innerAut_of_hasLabel hRlabel hφ3
  refine ggResSmallSpFour_J_innerOn_of_marking hP.1 ?_ hH.1.2.1.2.1.2 hP.2 hInner
  exact hH.1.2.2.1.2.2.2.2.2.1.2.2.1

open TableB

theorem ggResSmallSpFour_J_center_coprime_of_label
    {J : Type} [Group J] [Finite J]
    (hperf : commutator J = ⊤)
    (hLabel : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) ∨
      GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J)) :
    ∀ g ∈ Subgroup.center J, Nat.Coprime 3 (orderOf g) := by
  have hnotdvd : ¬ 3 ∣ Nat.card (Subgroup.center J) := by
    rcases hLabel with hC | hT
    · have hmod : StatedClassicalModel (J ⧸ Subgroup.center J) .PSp 3 2 1 :=
        ggResSmallSpFour_J_statedClassicalModel_C31 hC
      have hL : CFSG.Models.LieModel (J ⧸ Subgroup.center J) .PSp 3 2 1 :=
        ⟨hmod.1, Or.inl hmod⟩
      obtain ⟨-, ⟨e⟩⟩ :=
        CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_three_two_row hL
      exact CFSG.StandardType.ggPZMult_not_dvd_of_row hperf Nat.prime_three (by norm_num)
        (t := .PSp) (n := 3) (f := 1) ⟨e⟩
        (by norm_num [CFSG.Blueprint.Multiplier.genericOrders])
    · have hpsp : StatedClassicalModel (J ⧸ Subgroup.center J) .PSp 2 3 1 :=
        ggResSmallSpFour_J_statedClassicalModel_twA31 hT
      have hpsu : StatedClassicalModel (J ⧸ Subgroup.center J) .PSU 4 2 1 :=
        CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three hpsp
      have hL : CFSG.Models.LieModel (J ⧸ Subgroup.center J) .PSU 4 2 1 :=
        ⟨hpsu.1, Or.inl hpsu⟩
      obtain ⟨-, ⟨e⟩⟩ :=
        CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_four_two_row hL
      exact CFSG.StandardType.ggPZMult_not_dvd_of_row hperf Nat.prime_three (by norm_num)
        (t := .PSU) (n := 4) (f := 1) ⟨e⟩
        (by norm_num [CFSG.Blueprint.Multiplier.genericOrders])
  intro g hg
  have hdvd : orderOf g ∣ Nat.card (Subgroup.center J) := by
    rw [← Nat.card_zpowers g]
    exact Subgroup.card_dvd_of_injective
      (Subgroup.inclusion (Subgroup.zpowers_le.mpr hg))
      (fun a b hab => Subtype.ext
        (congrArg (fun x : ↥(Subgroup.center J) => (x : J)) hab))
  exact Nat.prime_three.coprime_iff_not_dvd.mpr fun h3 => hnotdvd (h3.trans hdvd)

theorem ggResSmallSpFour_J_card_ge_C3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (hC3 : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    48 ≤ Nat.card (ggAutomizer J Bs) := by
  obtain ⟨labM, hlabM, hLlabM, RM, instRM, IM, FM, θM, hPM⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hPM.1.1
  subst hp3
  have hInn : ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹ :=
    ggResSmallSpFour_J_innerOn hH hM (Or.inl hC3)
  have hZ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g) :=
    ggResSmallSpFour_J_center_coprime_of_label hH.1.2.2.1.2.2.2.2.2.1.2.2.1 (Or.inl hC3)
  exact ggR4J_card_ge_c3 hH.1.2.1.2.1 hH.1.2.1.2.2.2
    hH.1.2.2.1.2.2.2.2.2.1.2.2.1 hZ hInn hC3

theorem ggResSmallSpFour_J_card_eq_twA3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (hTwA : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    Nat.card (ggAutomizer J Bs) = 24 := by
  obtain ⟨labM, hlabM, hLlabM, RM, instRM, IM, FM, θM, hPM⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hPM.1.1
  subst hp3
  have hInn : ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹ :=
    ggResSmallSpFour_J_innerOn hH hM (Or.inr hTwA)
  have hZ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g) :=
    ggResSmallSpFour_J_center_coprime_of_label hH.1.2.2.1.2.2.2.2.2.1.2.2.1 (Or.inr hTwA)
  let Q₀ : LargeEvenRawCont :=
    fun R' _ _ _ => Nonempty (↥J ⧸ Subgroup.center ↥J ≃* R')
  have hRaw : LargeEvenRawDatum (⟨.twA, 3, 1⟩ : LargeEvenLabel) Q₀ := hTwA
  have hAutAll := ggPumpLineAutKnown_unitary_four_label (n := 1) (by norm_num)
    (by norm_num : 3 ∣ 2 ^ 1 + 1)
  have hRankAll := largeEvenLabelAll_torusSCRank_unitary (p := 3) Nat.prime_three
    (lab := ⟨.twA, 3, 1⟩) (by simp [LargeEvenInLambda2])
    (by simp [GGUnitaryCoprimeLabel])
  have hBoth := largeEvenLabelAll_and hAutAll hRankAll
  have hRaw2 := largeEvenRawDatum_inn_all (hBoth Q₀ hRaw)
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hRaw2
  obtain ⟨Kf, hF, hfin, hKf, hQP, hInnI⟩ := hRaw2
  obtain ⟨hQ₀, hAutP, hRankP⟩ := hQP
  letI := hF
  letI := hfin
  obtain ⟨θ⟩ := hQ₀
  have hRankP' : GGTorusSCRank 3 3
      (LargeEvenProj (LargeEvenSUGroup (Fin 4) Kf 2))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin 4) Kf 2)) := by
    simpa using hRankP
  exact ggAutomizer_card_eq_of_torusSCRank (N := 24) θ hInnI hRankP' hAutP
    hH.1.2.1.2.1 hH.1.2.1.2.2.2
    hH.1.2.2.1.2.2.2.2.2.1.2.2.1 hZ hInn

theorem ggResSmallSpFour_J_card_ge_24_of_label
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (hLab : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) ∨
      GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    24 ≤ Nat.card (ggAutomizer J Bs) := by
  rcases hLab with hC | hT
  · exact le_trans (by norm_num : 24 ≤ 48) (ggResSmallSpFour_J_card_ge_C3 hH hM hC)
  · exact (ggResSmallSpFour_J_card_eq_twA3 hH hM hT).ge

theorem ggResSmallSpFourExactTwo_false
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  obtain ⟨labM, hlabM, hLlabM, RM, instRM, IM, FM, θM, hPM⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hPM.1.1
  subst hp3
  have hLab : GGHasLabel (⟨.C, 3, 1⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) ∨
      GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) :=
    ggResSmallSpFour_exactTwo_C3_or_twA hH hM h2
  have hAL : Nat.card ↥(ggAutomizer L Bs) = 384 :=
    ggResSmallSpFour_automizerL_card hH hM
  have hX : ∃ c, GGWeylTypeData 4 (Nat.card ↥(ggAutomizer L Bs)) c := by
    refine ⟨2, ?_⟩
    rw [hAL]
    exact ggWeylTypeData_B4
  have hJne : ggAutomizer J Bs ≠ ⊥ :=
    (ggResLeviDatumCard_survivor_dvd_and_ne (p := 3) (k := 2) (n := 4) h2 hX
      (by norm_num) hH.Bs_le_normalizer_J (by norm_num) hH.1.2.1.2.1.2).2
  obtain ⟨Λ, hΛ, hcardΛ, r, hr, hW2⟩ :=
    ggResSmallSpFour_exactTwo_rank_two h2 hJne hAL
  subst hr
  have h24 : 24 ≤ Nat.card (ggAutomizer J Bs) :=
    ggResSmallSpFour_J_card_ge_24_of_label hH hM hLab
  have hle12 : Nat.card (ggAutomizer J Bs) ≤ 12 :=
    ggWeylTypeData_card_le_twelve_of_rank_le_two hW2 (by omega)
  omega


theorem ggResSmallSpFour_exactThree_L_rank_one
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h3 : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    Nat.card ↥(ggAutomizer J Bs) = 2 := by
  classical
  have hAL : Nat.card ↥(ggAutomizer L Bs) = 384 :=
    ggResSmallSpFour_automizerL_card hH hM
  have hX : GGWeylTypeData 4 384 2 := ggWeylTypeData_B4
  have hX' : GGWeylTypeData 4 (Nat.card ↥(ggAutomizer L Bs)) 2 := by
    rw [hAL]
    exact hX
  have hJ : ggAutomizer J Bs ≠ ⊥ :=
    (ggResLeviDatumCard_survivor_dvd_and_ne h3 ⟨2, hX'⟩ (by norm_num)
      hH.Bs_le_normalizer_J hH.1.1.2.2.2.2.2.1.2.1 hH.1.2.1.2.1.2).2
  obtain ⟨r, hr, hW⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData h3 hJ hX'
  have hr1 : r = 1 := by omega
  subst hr1
  rcases hW with ⟨-, hn, -⟩ | ⟨h2, -⟩ | ⟨h4, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ |
    ⟨h4, -⟩ | ⟨h2, -⟩
  · simpa using hn
  all_goals omega

theorem ggResSmallSpFour_exactThree_L_false
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h3 : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    False := by
  classical
  have hAJ2 : Nat.card ↥(ggAutomizer J Bs) = 2 :=
    ggResSmallSpFour_exactThree_L_rank_one hH hM h3
  obtain ⟨s, J', hs3, hs1, hcomp, ⟨eJ⟩, hlabels⟩ :=
    ggResSmallSpFour_component_labels hH hM
  rcases hlabels with hC3 | htwA | hB2
  · have h48 : 48 ≤ Nat.card ↥(ggAutomizer J Bs) :=
      ggResSmallSpFour_J_card_ge_C3 hH hM hC3
    omega
  · have h24 : Nat.card ↥(ggAutomizer J Bs) = 24 :=
      ggResSmallSpFour_J_card_eq_twA3 hH hM htwA
    omega
  · obtain ⟨lab, hlab, hLlab, R, instR, I, F, θ, hP⟩ :=
      largeEvenMarking_exists_hasLabel hM
    have hp3 : p = 3 := hP.1.1
    subst hp3
    have hAJ4 := hH.card_automizer_J_eq_four_of_A6
      (nonempty_alt6_of_B2der_transport hs3 hs1 hcomp eJ hB2)
    omega

theorem ggResSmallSpFour_card_bstar
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L) :
    Nat.card Bs = 3 ^ 5 := by
  obtain ⟨lab, hlab, hLlab, R, instR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hP.1.1
  have htag : lab.tag = .B ∨ lab.tag = .C := hP.1.2.1
  have hn1 : lab.n = 1 := hP.1.2.2.1
  have hrank4 : lab.rank = 4 := hP.1.2.2.2
  subst hp3
  have hZL : Subgroup.center ↥L = ⊥ :=
    HdRo7C.hdRo7CLOSpAux_center_L_eq_bot hH lab hlab hLlab htag hn1 (by omega)
  have hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ :=
    rank4_innerOnL hH lab hlab hLlab htag hn1 hrank4 rfl hP.2.1
  have hEcard := HdRo7C.hdRo7CLOSpAux_card_inf_pow hH lab hlab hLlab htag hn1
    (by omega) rfl hP.2.1 hInnL
  have hCeq := HdRo7C.hdRo7CLCoordAux_bstar_centralizer_eq hH
  have hCcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = 3 := by
    rw [hCeq, Nat.card_zpowers]
    exact orderOf_eq_prime (HdRo7C.hdRo7CLCoordAux_x_pow_eq_one hH)
      (HdRo7C.hdRo7CLCoordAux_x_ne_one hH)
  have hsplit := card_ggBstar_split hH.1.2.1 hZL hP.2.1 hInnL
  rw [hEcard, hrank4, hCcard] at hsplit
  simpa using hsplit

theorem ggResSmallSpFour_exactThree_K_false
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  classical
  obtain ⟨lab, hlab, hLlab, R, instR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  have hp3 : p = 3 := hP.1.1
  subst hp3
  have hBsCard := ggResSmallSpFour_card_bstar hH hM
  have hJCard : Nat.card (ggAutomizer J Bs) = 4 ∨ 24 ≤ Nat.card (ggAutomizer J Bs) := by
    obtain ⟨s, J', hs3, hs1, hcomp, ⟨eJ⟩, hlabels⟩ := ggResSmallSpFour_component_labels hH hM
    rcases hlabels with hC | hT | hA
    · exact Or.inr ((by norm_num : 24 ≤ 48).trans (ggResSmallSpFour_J_card_ge_C3 hH hM hC))
    · exact Or.inr (ggResSmallSpFour_J_card_eq_twA3 hH hM hT).ge
    · exact Or.inl (hH.card_automizer_J_eq_four_of_A6
        (nonempty_alt6_of_B2der_transport hs3 hs1 hcomp eJ hA))
  have hJne : ggAutomizer J Bs ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hJCard
    rcases hJCard with h | h <;> omega
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := h3
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hVcard : Nat.card V = 3 ^ 5 := by
    calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = 3 ^ 5 := hBsCard
  have hdim : Module.finrank (ZMod 3) V = 5 := by
    have hp := FiniteField.pow_finrank_eq_natCard 3 V
    rw [hVcard] at hp
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hp
  have hn : Fintype.card Λ ≤ 5 := by
    have haxis := ggResK_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w)
      hpairL hCLL.1 hclosL
    have hcart := ggIntCartan_card_le_rank_add_one hWML hCLL 3 (by norm_num)
    omega
  have hX : GGWeylTypeData (Fintype.card Λ) (Nat.card (ggAutomizer K Bs))
      (Nat.card (Subgroup.center ML.Group)) := by
    have hh := ggWeylTypeData_of_isWeylMatrix hWML
    have hc : Nat.card ML.Group = Nat.card (ggAutomizer K Bs) := Nat.card_congr fL.toEquiv
    rwa [hc] at hh
  have h3' : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny :=
    ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩
  obtain ⟨r, hr, hW⟩ := ggResLeviDatumCard_rank_eq_of_weylTypeData h3' hJne hX
  have hr2 : r ≤ 2 := by omega
  rcases hJCard with h4 | h24
  · rw [h4] at hW
    rcases hW with ⟨_, hn, _⟩ | ⟨_, hn, _⟩ | ⟨hn, _⟩ | ⟨hn, _⟩ | ⟨hn, _⟩ | ⟨hn, _⟩ |
      ⟨hn, _⟩ | ⟨_, hn, _⟩
    all_goals interval_cases r <;> norm_num at *
  · have h12 := ggWeylTypeData_card_le_twelve_of_rank_le_two hW hr2
    omega

theorem ggResSmallSpFour_not_exactThree_either
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L) :
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
  rintro (h3 | h3)
  · exact ggResSmallSpFour_exactThree_L_false hH hM h3
  · exact ggResSmallSpFour_exactThree_K_false hH hM h3

end CFSG.StandardType

end

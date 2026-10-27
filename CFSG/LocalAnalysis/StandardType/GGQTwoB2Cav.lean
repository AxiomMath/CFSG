module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeAltSix
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltMaxThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltLocal
public import CFSG.LocalAnalysis.AGLEmbedding.AltSix
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGB48OmReduce
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoOriginalNormalizerLift
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallAutFix
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallShape
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRNoX
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic

public noncomputable section

namespace CFSG.StandardType.QTwoB2Cav

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.SmallIdent
  CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltSix

variable {K : Type} [Group K] [Finite K]

theorem centralizer_sylow_eq (hK : IsAltTwoP 3 K) (P : Sylow 3 K) :
    Subgroup.centralizer ((P : Subgroup K) : Set K) = (P : Subgroup K) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPcard : Nat.card (P : Subgroup K) = 9 := by
    simpa using sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hK P
  have hcomm : IsMulCommutative (P : Subgroup K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hPcard
  have hPC : (P : Subgroup K) ≤ Subgroup.centralizer ((P : Subgroup K) : Set K) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm
  obtain ⟨e⟩ := hK
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup K)) 3
    (by rw [hPcard]; norm_num)
  have ha3 : orderOf (a : K) = 3 := by rwa [Subgroup.orderOf_mk] at ha
  have hCa : Subgroup.centralizer ((P : Subgroup K) : Set K) ≤
      Subgroup.centralizer ({(a : K)} : Set K) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr a.property)
  apply (Subgroup.eq_of_le_of_card_ge hPC ?_).symm
  rw [hPcard]
  exact (Subgroup.card_le_of_le hCa).trans (card_centralizer_le_nine e ha3)

theorem card_automizer_sylow (hK : IsAltTwoP 3 K) (P : Sylow 3 K) :
    Nat.card (ggAutomizer (⊤ : Subgroup K) (P : Subgroup K)) = 4 := by
  let N := Subgroup.normalizer ((P : Subgroup K) : Set K)
  have hrange : (P : Subgroup K).normalizerMonoidHom.range =
      ggAutomizer (⊤ : Subgroup K) (P : Subgroup K) := by
    ext φ
    rw [mem_ggAutomizer_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, Subgroup.mem_top _, u.property, fun _ => rfl⟩
    · rintro ⟨g, _, hg, hφ⟩
      exact ⟨⟨g, hg⟩, MulEquiv.ext fun b => Subtype.ext (hφ b).symm⟩
  have hkerCard : Nat.card (P : Subgroup K).normalizerMonoidHom.ker = 9 := by
    rw [Subgroup.normalizerMonoidHom_ker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer ((P : Subgroup K) : Set K))).toEquiv,
      centralizer_sylow_eq hK P]
    simpa using sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hK P
  have hcard := Subgroup.card_ker_mul_card_range (P : Subgroup K).normalizerMonoidHom
  rw [hkerCard, hrange, card_normalizer hK P] at hcard
  omega

theorem exists_sylow_eq_of_selfCentralizing (hK : IsAltTwoP 3 K)
    {E : Subgroup K} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hSC : ∀ k ∈ Subgroup.centralizer (E : Set K), k ^ 3 = 1 → k ∈ E) :
    ∃ P : Sylow 3 K, (P : Subgroup K) = E := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hEP⟩ := hE.isPGroup.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hEP⟩
  intro k hk
  apply hSC k ?_ (pow_eq_one_of_mem_isAltTwoP Nat.prime_three (by norm_num) hK P hk)
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact mul_comm_of_mem_isAltTwoP Nat.prime_three (by norm_num) hK P (hEP he) hk

variable {G : Type} [Group G] [Finite G] {B Bs J : Subgroup G}

theorem inner_action_of_isAltTwoP (hJ : IsAltTwoP 3 J)
    (hBs : CFSG.Assembly.IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    ∀ b ∈ Bs, ∃ j ∈ J, ∀ k ∈ J, b * k * b⁻¹ = j * k * j⁻¹ := by
  obtain ⟨e⟩ := hJ
  intro b hb
  let a := J.normalizerMonoidHom ⟨b, hN hb⟩
  have ha3 : a ^ 3 = 1 := by
    change (J.normalizerMonoidHom ⟨b, hN hb⟩) ^ 3 = 1
    rw [← map_pow]
    have hb3 : (⟨b, hN hb⟩ : Subgroup.normalizer (J : Set G)) ^ 3 = 1 :=
      Subtype.ext (hBs.2 b hb)
    rw [hb3, map_one]
  have hae3 : (MulAut.congr e a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  obtain ⟨j, hj⟩ := CFSG.AGLEmbedding.mem_range_conj_of_pow_eq_one
    Nat.prime_three (by norm_num) hae3
  have ha : a = MulAut.conj (e.symm j) := by
    apply (MulAut.congr e).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
      MulEquiv.apply_symm_apply]
    exact hj.symm
  refine ⟨e.symm j, (e.symm j).property, ?_⟩
  intro k hk
  exact congrArg (fun f : MulAut J => ((f ⟨k, hk⟩ : J) : G)) ha

theorem card_automizer_original_of_isAltTwoP (hBs : GGBstar 3 B Bs)
    (hJ : IsAltTwoP 3 J) (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card (ggAutomizer J Bs) = 4 := by
  have hZ : Subgroup.center J = ⊥ :=
    center_eq_bot_of_isAltTwoP Nat.prime_three (by norm_num) hJ
  have hinner := inner_action_of_isAltTwoP hJ hBs.2.1 hN
  let E : Subgroup J := (Bs ⊓ J).subgroupOf J
  have hE : CFSG.Assembly.IsElemAbelian 3 E :=
    (hBs.2.1.mono inf_le_left).subgroupOf J
  have hSC : ∀ k ∈ Subgroup.centralizer (E : Set J), k ^ 3 = 1 → k ∈ E := by
    intro k hk hkp
    apply B48Om.mem_inf_of_commute hBs hZ hinner k.property ?_
      (congrArg Subtype.val hkp)
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hk (⟨e, he.2⟩ : J) he)
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_selfCentralizing hJ hE hSC
  have hmap : E.map J.subtype = Bs ⊓ J :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hcard : Nat.card (ggAutomizer J (Bs ⊓ J)) =
      Nat.card (ggAutomizer (⊤ : Subgroup J) E) := by
    have h := F4AutWeyl.ggAutomizer_map_eq J.subtype_injective (⊤ : Subgroup J) E hmap
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    rw [h, Subgroup.card_map_of_injective (MulAut.congr _).injective]
  rw [B48Om.ggAutomizer_card_eq hBs hZ hinner, hcard, ← hP]
  exact card_automizer_sylow hJ P

theorem card_automizer_original_of_setting {p : ℕ} {x : G} {L D : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hJ : IsAltTwoP 3 J) :
    Nat.card (ggAutomizer J Bs) = 4 := by
  subst p
  exact card_automizer_original_of_isAltTwoP hS.1.1.2.1 hJ
    (QTwoCav.bstar_le_normalizer_j hS hN)

end CFSG.StandardType.QTwoB2Cav

end

module

public import CFSG.RankThree.GF2n.Tim81.Sec8.Assembly
public import CFSG.Quasithin.Background.SmallModelNormal
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.GH74.Bender
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.GroupTheory.TISylowLocal
public import CFSG.Quasithin.H13.NQRigidFacts

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.Assembly CFSG.Open
open CFSG.Quasithin.H13.NQRigid (isMaximalTwoLocal_iff_quasithinIsMaxTwoLocal)

variable {G : Type} [Group G] [Finite G]

section


private theorem false_of_fusionIsBenderGroup {M V : Subgroup G} {T : Sylow 2 G}
    [IsSimpleGroup G] (hB : fusionIsBenderGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hHyp : Hyp M V) (hTM : (T : Subgroup G) ≤ M)
    (hwcQ : CFSG.CGT.Timmesfeld75.WeaklyClosedIn V (inSubgroup (pCore 2) M))
    (hnwc : ¬ CFSG.CGT.Timmesfeld75.WeaklyClosedIn V M) :
    False := by
  have hB' : CFSG.BenderSuzuki.IsBenderGroup G :=
    CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup hB
  have hTI : CFSG.CGT.Timmesfeld75.IsTI (T : Subgroup G) :=
    CFSG.GroupTheory.isTI_of_isStronglyEmbeddedOrder_normalizer
      (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hB' T)
  exact hnwc (CFSG.GroupTheory.weaklyClosedIn_of_isTI_sylow hnonab hHyp.maxLocal hTM hTI
    hHyp.le_M hwcQ)

private theorem false_of_uniqueSmallModel {M V : Subgroup G} {T : Sylow 2 G}
    (hS : CFSG.QuasithinUnique.UniqueSmallModel G) (hHyp : Hyp M V)
    (hTM : (T : Subgroup G) ≤ M) (hV4 : 4 ≤ Nat.card V) : False := by
  have hVT : V ≤ (T : Subgroup G) :=
    sup_eq_right.mp (T.is_maximal'
      (hHyp.isPGroup_V.to_sup_of_normal_left' T.isPGroup'
        (hTM.trans hHyp.le_normalizer)) le_sup_right)
  have hN : (T : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
    hTM.trans hHyp.le_normalizer
  exact CFSG.Quasithin.RonanE628.MathAS4.not_uniqueSmallModel_of_normal_elemAbelian
    T hHyp.elem hVT hN (by omega) hS

theorem sec8SmallRankStatement_of_thm211 (h211 : CFSG.Quasithin.RonanE628.MathAS4.Thm211) :
    Sec8SmallRankStatement := by
  intro G _ _ _ hnonab hK hchar M V hHyp hV4 hwcQ hnwc _ hsyl hrk
  have hchar' : CFSG.Assembly.IsCharTwoType G := CFSG.GH74.isCharTwoType_iff.mpr hchar
  have hgen : CFSG.GH74.Gen4 G := hrk
  have he : CFSG.Assembly.evenRank G ≤ 2 :=
    CFSG.GH74.evenRank_le_two_of_charTwoType_gen4 hchar' hgen
  have hKC : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G :=
    CFSG.Assembly.KProper.of_catalogImp CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge
      (CFSG.ComponentClassification.CatalogueKProper.kProper_of_isKProper hK)
  have hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G :=
    CFSG.Assembly.Quasithin.QTKEOver.of_isCharTwoType hKC hchar' he
  have hcore : CFSG.QuasithinUnique.QTKECore G :=
    CFSG.QuasithinUnique.qtkeCore_of_cat hnonab hqtke
  obtain ⟨T, hTM, hTuniq⟩ := hsyl.exists_sylow
  have hTunique : ∃! M : Subgroup G,
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M := by
    refine ⟨M, ⟨isMaximalTwoLocal_iff_quasithinIsMaxTwoLocal.mp hHyp.maxLocal, hTM⟩, ?_⟩
    rintro M' ⟨hM', hTM'⟩
    exact hTuniq M' (isMaximalTwoLocal_iff_quasithinIsMaxTwoLocal.mpr hM') hTM'
  obtain ⟨M₀, hUS⟩ := CFSG.QuasithinUnique.uniqueSetting_of_sylow hnonab hcore T hTunique
  rcases h211 G (T : Subgroup G) M₀ hUS with hB | hS
  · exact false_of_fusionIsBenderGroup hB hnonab hHyp hTM hwcQ hnwc
  · exact false_of_uniqueSmallModel hS hHyp hTM hV4

end

section


theorem sec8SmallRankStatement
    :
    Sec8SmallRankStatement :=
  sec8SmallRankStatement_of_thm211 CFSG.QuasithinUnique.theorem_2_1_1_proved

end

end CFSG.RankThree.GF2n.Tim81

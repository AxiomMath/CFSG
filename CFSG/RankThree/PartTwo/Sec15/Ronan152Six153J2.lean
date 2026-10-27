module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152Six153Main
public import CFSG.RankThree.PartTwo.Sec15.Ronan152Six153Core
public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixHelpers
public import CFSG.RankThree.PartTwo.Sec15.F153Leaf
public import CFSG.HardMathSupport.Cooperstein.Proving.SporadicNoIrrFF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan152Six

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec15
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Proving (noIrrFFOffender_J2)

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic (noIrrFFOffender_transfer)


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem center_J2_eq_bot_of_mulEquiv {Q : Type} [Group Q]
    (hq : CFSG.IsQuasisimple Q) (e : Q ≃* CFSG.Blueprint.NativeSporadic.J2) :
    Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := by
  refine CFSG.RankThree.PartTwo.Sec15.center_eq_bot_of_isSimpleGroup
    CFSG.Sporadic.J2.isSimpleGroup_J2 ?_
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨e a, e b, fun h => hab ?_⟩
  have h' : a * b = b * a := e.injective (by rw [map_mul, map_mul, h])
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']

theorem hasFaithfulE9_of_isJ2Type
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hJ : IsJ2Type Y) : HasFaithfulE9 Y := by
  obtain ⟨e⟩ := hJ
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  obtain ⟨E, hE, h9⟩ := CFSG.QuasithinUnique.Id2519.exists_elemAbelian_nine_J2
  exact hasFaithfulE9_of_mulEquiv hq e (center_J2_eq_bot_of_mulEquiv hq e)
    ⟨E, hE, by rw [h9]; norm_num⟩

theorem le_normalizer_of_isJ2Type
    (h : Sec14Std G A c L) (h152 : Item152Big A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hJ : IsJ2Type Y) :
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      M ≤ Subgroup.normalizer (Y : Set G) :=
  fun _ hM _ ht => Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (map_conj_eq_of_hasFaithfulE9_big h h152 hY hJ.big152 (hasFaithfulE9_of_isJ2Type hY hJ) hM ht)

section Certs


theorem charNormal153_of_isJ2Type (hM2 : ThmC.KFactM2) (h148 : Item148R)
    (h149 : Sec16.Item149S14) (h142 : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14)
    (h1444 : Item1444S14) (hbot : Item145BotS14) (hL3 : ThmD.L3FieldFusionK)
    (hP4 : ThmD.Step148FourKFact) (hR : Sec15R G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hJ : IsJ2Type Y)
    (hn : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      M ≤ Subgroup.normalizer (Y : Set G))
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2)) :
    CharNormal153 Y S := by
  by_contra hno
  have hh := hR.toSec14Std
  have h149' : Item149 A (lB A) := h149 G A c L hh
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) :=
    hS.prop.1.2.trans (n155_le_normalizer_of_forall_le_normalizer hh h149' hY hn)
  have hO : CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S :=
    pCoreOf_sup_le_of_le_normalizer hM2 h148 h142 h143 h146 h1444 hbot hL3 hP4 hR hY hS hSY
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hS1 : S ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq] at hO
    exact hY.prop.2.2 (le_bot_iff.mp hO)
  have hFF : FF153 Y S :=
    ⟨hO, fun hJS => hno (Push153.charNormal153_of_thompsonJ_le hS2 hS1 hO hJS)⟩
  have hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y :=
    generalizedFitting_eq_of_forall_le_normalizer hh h149' hY hn
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  obtain ⟨e⟩ := hJ
  obtain ⟨e'⟩ :=
    F153.nonempty_centerQuotient_equiv_of_simple hYq CFSG.Sporadic.J2.isSimpleGroup_J2 e
  have hirr : NoIrrFFOffender CFSG.Blueprint.NativeSporadic.J2 :=
    noIrrFFOffender_transfer noIrrFFOffender_J2
      ⟨(CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv.some).symm⟩
  have hKP : CFSG.Open.IsKProper G := hh.toTheoremFourHyp.kProper
  have hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S) :=
    hKP.isKGroup (Y ⊔ S) (F153.sup_ne_top_of_pCoreOf_ne_bot hh.toTheoremFourHyp hSY hY.prop.2.2)
  exact F153.leaf_false_of_noFFModule hKH hF hY.prop.1.2.1 hYq hS2 hSY hFF hno
    (noFFModule_of_noIrrFFOffender hirr) e'

theorem item153MainJ2_of (hM2 : ThmC.KFactM2) (h148 : Item148R)
    (h149 : Sec16.Item149S14) (h142 : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14)
    (h1444 : Item1444S14) (hbot : Item145BotS14) (hL3 : ThmD.L3FieldFusionK)
    (hP4 : ThmD.Step148FourKFact) (hR : Sec15R G A c L) (h152 : Item152Big A (lB A)) :
    Item153MainJ2 A (lB A) := by
  intro Y hY hJ
  have hh := hR.toSec14Std
  have hn := le_normalizer_of_isJ2Type hh h152 hY hJ
  exact item153Main_at_of_forall_le_normalizer hh (h149 G A c L hh) hY hn fun S hS =>
    charNormal153_of_isJ2Type hM2 h148 h149 h142 h143 h146 h1444 hbot hL3 hP4 hR hY hJ hn hS

theorem item153MainJ2R_of (hM2 : ThmC.KFactM2) (h148 : Item148R)
    (h149 : Sec16.Item149S14) (h142 : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14)
    (h1444 : Item1444S14) (hbot : Item145BotS14) (hL3 : ThmD.L3FieldFusionK)
    (hP4 : ThmD.Step148FourKFact) (h152 : Item152BigR) : Item153MainJ2R :=
  fun _ _ _ _ _ _ hR => item153MainJ2_of hM2 h148 h149 h142 h143 h146 h1444 hbot hL3 hP4 hR
    (h152 _ _ _ _ hR)

end Certs

end CFSG.RankThree.PartTwo.Sec15.Ronan152Six

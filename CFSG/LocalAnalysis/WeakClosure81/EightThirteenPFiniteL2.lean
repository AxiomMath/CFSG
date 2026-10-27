module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFiniteL2F1
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFiniteL2F2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagProducts
import CFSG.GroupTheory.AlternatingFive.SylowTwo
import CFSG.Quasithin.Background.C48AsmLine
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagCovers
import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
import CFSG.Quasithin.Background.C124AsmClassify
import CFSG.Quasithin.Background.C124Interface
import CFSG.Quasithin.Background.C124YZStar
import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
import CFSG.Quasithin.Vol2.Ch12Sec6L23c
import CFSG.Quasithin.Vol2.Ch12Sec6P31Fin
import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl
import CFSG.Quasithin.Vol2.Ch12Sec6P31WXA
import CFSG.Quasithin.Vol2.Ch12Sec6P31WXB
import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
import CFSG.RankThree.PartOne.CTP.SpEven
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec4.Item426A6
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec8.Steps
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import CFSG.Walter.W67.Statements

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3 IsL3 IsSp4 IsSL3)

private theorem wc813fl2_borelRankOne_of_coatom
    {Y : Type} [Group Y] [Finite Y] (L S : Subgroup Y) (hSL : S ≤ L)
    (hP : IsPGroup 2 (S.subgroupOf L)) (hnd : ¬ 2 ∣ (S.subgroupOf L).index)
    (hcoat : IsCoatom (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L))) :
    ∀ P : Subgroup Y, L ⊓ normalizer (S : Set Y) ≤ P → P ≤ L →
      P = L ⊓ normalizer (S : Set Y) ∨ P = L := by
  intro P hBP hPL
  have hB : (L ⊓ normalizer (S : Set Y)).subgroupOf L =
      Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hSL]
  have hle : (L ⊓ normalizer (S : Set Y)).subgroupOf L ≤ P.subgroupOf L :=
    Subgroup.subgroupOf_mono L hBP
  rcases isCoatom_iff_ge_of_le.mp hcoat with ⟨-, hmax⟩
  by_cases htop : P.subgroupOf L = ⊤
  · right
    have h1 : P ⊓ L = (⊤ : Subgroup Y) ⊓ L :=
      (Subgroup.subgroupOf_inj).mp (by rw [htop, Subgroup.top_subgroupOf])
    rw [inf_eq_left.mpr hPL, top_inf_eq] at h1
    exact h1
  · left
    have hple : P.subgroupOf L ≤ (L ⊓ normalizer (S : Set Y)).subgroupOf L := by
      rw [hB]
      exact hmax (P.subgroupOf L) htop (hB ▸ hle)
    have heq : P.subgroupOf L = (L ⊓ normalizer (S : Set Y)).subgroupOf L :=
      le_antisymm hple hle
    have h1 : P ⊓ L = (L ⊓ normalizer (S : Set Y)) ⊓ L :=
      (Subgroup.subgroupOf_inj).mp heq
    rw [inf_eq_left.mpr hPL, inf_eq_left.mpr inf_le_left] at h1
    exact h1

private theorem wc813fl2_card_of_isL2 {X : Type} [Group X]
    (h : IsL2 X 2) : Nat.card X = 60 := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model X h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem wc813fl2_isSimpleGroup_of_isL2 {X : Type} [Group X] (h : IsL2 X 2) :
    IsSimpleGroup X :=
  CFSG.Quasithin.C48.isSimpleGroup_psl_two (p := 2) (e := 2)
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

private theorem wc813fl2_card_sylow_of_isL2
    {Y : Type} [Group Y] [Finite Y] {L S : Subgroup Y} (hL2 : IsL2 ↥L 2)
    (hSL : S ≤ L) (hP : IsPGroup 2 (S.subgroupOf L))
    (hnd : ¬ 2 ∣ (S.subgroupOf L).index) : Nat.card ↥S = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model ↥L hL2
  let P'' : Sylow 2 (alternatingGroup (Fin 5)) :=
    (hP.map e.toMonoidHom).toSylow (Subgroup.index_map_equiv (S.subgroupOf L) e ▸ hnd)
  have hcoe : (P'' : Subgroup (alternatingGroup (Fin 5))) =
      (S.subgroupOf L).map e.toMonoidHom := IsPGroup.toSylow_coe _ _
  calc Nat.card ↥S = Nat.card ↥(S.subgroupOf L) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv).symm
    _ = Nat.card ↥((S.subgroupOf L).map e.toMonoidHom) :=
        Nat.card_congr (e.subgroupMap (S.subgroupOf L)).toEquiv
    _ = Nat.card ↥P'' := (Nat.card_congr (MulEquiv.subgroupCongr hcoe).toEquiv).symm
    _ = 4 := CFSG.GroupTheory.AlternatingFive.card_sylow_two_eq P''

private theorem wc813fl2_relIndex_normalizer_eq_five
    {Y : Type} [Group Y] [Finite Y] {L S : Subgroup Y} (hL2 : IsL2 ↥L 2)
    (hSL : S ≤ L) (hP : IsPGroup 2 (S.subgroupOf L))
    (hnd : ¬ 2 ∣ (S.subgroupOf L).index) :
    (L ⊓ normalizer (S : Set Y)).relIndex L = 5 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model ↥L hL2
  have hB : (L ⊓ normalizer (S : Set Y)).subgroupOf L =
      Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hSL]
  rw [Subgroup.relIndex, hB]
  have hmap : (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)).map
        e.toMonoidHom =
      Subgroup.normalizer (((S.subgroupOf L).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))) :=
    Subgroup.map_equiv_normalizer_eq (S.subgroupOf L) e
  have hstep : (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)).index =
      (Subgroup.normalizer (((S.subgroupOf L).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))).index := by
    calc (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)).index
        = ((Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)).map
            e.toMonoidHom).index :=
          (Subgroup.index_map_equiv
            (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)) e).symm
      _ = _ := by rw [hmap]
  rw [hstep]
  let P'' : Sylow 2 (alternatingGroup (Fin 5)) :=
    (hP.map e.toMonoidHom).toSylow (Subgroup.index_map_equiv (S.subgroupOf L) e ▸ hnd)
  have hcoe : (P'' : Subgroup (alternatingGroup (Fin 5))) =
      (S.subgroupOf L).map e.toMonoidHom := IsPGroup.toSylow_coe _ _
  have hstep2 : (Subgroup.normalizer (((S.subgroupOf L).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))).index =
      (Subgroup.normalizer (P'' : Set (alternatingGroup (Fin 5)))).index :=
    congrArg (fun H : Subgroup (alternatingGroup (Fin 5)) =>
      (Subgroup.normalizer (H : Set (alternatingGroup (Fin 5)))).index) hcoe.symm
  rw [hstep2]
  have hcardN : Nat.card ↥(Subgroup.normalizer (P'' : Set (alternatingGroup (Fin 5)))) = 12 :=
    CFSG.GroupTheory.AlternatingFive.card_normalizer_sylow_two P''
  have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hmul := Subgroup.card_mul_index
    (Subgroup.normalizer (P'' : Set (alternatingGroup (Fin 5))))
  rw [hcardN, hcardA] at hmul
  omega

private theorem wc813fl2_oTwoMod_bot_eq_bot {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y)
    (hsimple : IsSimpleGroup ↥L) (hcard : Nat.card ↥L = 60) :
    oTwoMod (⊥ : Subgroup Y) L = ⊥ := by
  rw [oTwoMod]
  refine le_antisymm (iSup₂_le fun W hW => ?_) bot_le
  have hWL : W ≤ L := hW.2.1
  have hWnorm : (W.subgroupOf L).Normal := hW.2.2.1
  have hW2 : IsPGroup 2 W := by
    intro w
    obtain ⟨k, hk⟩ := hW.2.2.2 (w : Y) w.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  haveI := hWnorm
  rcases hsimple.eq_bot_or_eq_top_of_normal (W.subgroupOf L) with h | h
  · rw [← Subgroup.map_subgroupOf_eq_of_le hWL, h, Subgroup.map_bot]
  · exfalso
    have hWL' : W = L := by
      have h1 : W = (⊤ : Subgroup ↥L).map L.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hWL, h]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      exact h1
    have hPL : IsPGroup 2 ↥L := hWL' ▸ hW2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥L)).mp hPL
    rw [hcard] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

private theorem wc813fl2_hasQuotShape_of_oTwoMod_eq_bot {Y : Type} [Group Y] {L : Subgroup Y}
    (hL2 : IsL2 ↥L 2) (h : oTwoMod (⊥ : Subgroup Y) L = ⊥) :
    HasQuotShape L (oTwoMod (⊥ : Subgroup Y) L : Set Y) (fun X _ => IsL2 X 2) := by
  rw [h]
  refine ⟨↥L, inferInstance, MonoidHom.id ↥L, fun x => ⟨x, rfl⟩, ?_, hL2⟩
  intro k
  show MonoidHom.id ↥L k = 1 ↔ (k : Y) ∈ (⊥ : Subgroup Y)
  rw [Subgroup.mem_bot]
  exact Subtype.ext_iff

theorem involutionCentralizerOn_L2 :
    InvolutionCentralizerOn ShapeL2 :=
  wc813fl2_involutionCentralizerOn_L2

theorem fourGroupInnerOn_L2 : FourGroupInnerOn ShapeL2 :=
  wc813fl2_fourGroupInnerOn_L2

theorem borelRankOneOn_L2 : BorelRankOneOn ShapeL2 := by
  intro Y _ _ L S hL hSy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL : S ≤ L := hSy.1
  have hP : IsPGroup 2 (S.subgroupOf L) :=
    hSy.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  have hnd : ¬ 2 ∣ (S.subgroupOf L).index := hSy.not_dvd_relIndex
  have hcoat : IsCoatom (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)) := by
    have hcoe : ((hP.toSylow hnd : Sylow 2 ↥L) : Set ↥L) =
        ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      congrArg (fun H : Subgroup ↥L => (H : Set ↥L)) (IsPGroup.toSylow_coe hP hnd)
    have h := CFSG.LocalAnalysis.UniquenessCase.UC22.coatom_normalizer_sylow_of_isL2 hL.2
      (hP.toSylow hnd)
    rwa [hcoe] at h
  exact wc813fl2_borelRankOne_of_coatom L S hSL hP hnd hcoat

theorem borelRankOneOn_U3 : BorelRankOneOn ShapeU3 := by
  intro Y _ _ L S hL hSy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL : S ≤ L := hSy.1
  have hP : IsPGroup 2 (S.subgroupOf L) :=
    hSy.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  have hnd : ¬ 2 ∣ (S.subgroupOf L).index := hSy.not_dvd_relIndex
  have hcoat : IsCoatom (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)) := by
    have hcoe : ((hP.toSylow hnd : Sylow 2 ↥L) : Set ↥L) =
        ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      congrArg (fun H : Subgroup ↥L => (H : Set ↥L)) (IsPGroup.toSylow_coe hP hnd)
    have h := CFSG.LocalAnalysis.UniquenessCase.UC22.coatom_normalizer_sylow_of_isU3 hL.2
      (hP.toSylow hnd)
    rwa [hcoe] at h
  exact wc813fl2_borelRankOne_of_coatom L S hSL hP hnd hcoat

theorem choiceOfKOn_L2 : ChoiceOfKOn ShapeL2 := by
  intro Y _ _ L S A hL hSy hAS hAe hA4 _ _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL : S ≤ L := hSy.1
  have hP : IsPGroup 2 (S.subgroupOf L) :=
    hSy.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  have hnd : ¬ 2 ∣ (S.subgroupOf L).index := hSy.not_dvd_relIndex
  have hLcard : Nat.card ↥L = 60 := wc813fl2_card_of_isL2 hL.2
  have hsimple : IsSimpleGroup ↥L := wc813fl2_isSimpleGroup_of_isL2 hL.2
  have hoTwo : oTwoMod (⊥ : Subgroup Y) L = ⊥ :=
    wc813fl2_oTwoMod_bot_eq_bot L hsimple hLcard
  have hScard : Nat.card ↥S = 4 :=
    wc813fl2_card_sylow_of_isL2 hL.2 hSL hP hnd
  have hScomm : ∀ a ∈ A, ∀ s ∈ S, a * s = s * a := by
    intro a ha s hs
    have hcard : Nat.card ↥S = 2 ^ 2 := by rw [hScard]; norm_num
    have hcomm := IsPGroup.commutative_of_card_eq_prime_sq (p := 2) (G := ↥S) hcard
    exact congrArg Subtype.val (hcomm ⟨a, hAS ha⟩ ⟨s, hs⟩)
  refine ⟨L, le_rfl, hAS.trans hSL, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hoTwo]
    intro hAle
    have h1 : A = ⊥ := le_bot_iff.mp hAle
    rw [h1, Subgroup.card_bot] at hA4
    omega
  · exact wc813fl2_hasQuotShape_of_oTwoMod_eq_bot hL.2 hoTwo
  · rwa [inf_eq_left.mpr hSL]
  · rw [show L ⊓ (L ⊓ normalizer (S : Set Y)) = L ⊓ normalizer (S : Set Y) by
      rw [← inf_assoc, inf_idem]]
    exact wc813fl2_relIndex_normalizer_eq_five hL.2 hSL hP hnd
  · intro _ hnot
    exact absurd hScomm hnot

theorem finiteFacts_of_shapes (hC : CitedShapeFacts)
    (hG : GapShapeFacts) :
    InvolutionCentralizerFact ∧ FourGroupInnerFact ∧ BorelOvergroupFact ∧ ChoiceOfKFact ∧
      BorelGL32Fact :=
  ⟨InvolutionCentralizerFact.of_shapes involutionCentralizerOn_L2 hC.f1_U3 hC.f1_L3 hC.f1_Sp4
      hC.f1_SL3,
    FourGroupInnerFact.of_shapes fourGroupInnerOn_L2 hC.f2_U3 hC.f2_L3 hC.f2_Sp4 hC.f2_SL3,
    BorelOvergroupFact.of_shapes borelRankOneOn_L2 borelRankOneOn_U3 hC.f3_L3 hC.f3_Sp4 hC.f3_SL3,
    ChoiceOfKFact.of_shapes choiceOfKOn_L2 hG.f4_U3 hG.f4_L3 hG.f4_Sp4 hG.f4_SL3,
    BorelGL32Fact.of_shapes hG.f6_U3 hG.f6_L3 hG.f6_Sp4 hG.f6_SL3⟩

end CFSG.LocalAnalysis.WeakClosure81

end

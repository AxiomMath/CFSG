module

public import CFSG.Quasithin.EmptyFaithful.S1421QA20Fam
public import CFSG.Quasithin.EmptyFaithful.A38c4Main
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.LieType.Simplicity.TrialityD4
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.Quasithin.S1421QA20

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Open (ordG2 ordTrialityD4 ordTwistedF4)

theorem a318Exclusion_big_sp4 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel X .PSp 2 2 f) : A318Exclusion X := by
  have hsimp : IsSimpleGroup X :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 2 2 f h
  have hrank := CFSG.Quasithin.R3c3.two_le_pRank_three_isPSp_two h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hbot := CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot
    (K := K) 2
  let e' : X ≃* ↥(StatedSp 2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)
  obtain ⟨-, -, hno⟩ := factA318Excl_holds.1 K f hf hK
  refine ⟨hsimp, hrank, ?_⟩
  intro Y _ s p k _ _ hY _ g hg
  exact (hno Y s p k hY).1 (e'.toMonoidHom.comp g) (e'.surjective.comp hg)

theorem a318Exclusion_big_g2 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel X .G2 2 f) : A318Exclusion X := by
  have hsimp := (CFSG.LieType.Simplicity.fam_g2_simplicity X 2 f h).2
  have hrank := CFSG.Quasithin.R3c3.two_le_pRank_three_isG2 (f := f) (X := X) h
  have hN : Nat.card X = ordG2 (2 ^ f) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  exact A318Exclusion.of_card hsimp hrank hN (l3Free_ordG2 hf)

theorem a318Exclusion_big_3d4 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel X .trialityD4 2 f) : A318Exclusion X := by
  have hsimp := (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 f h).2
  have hrank := CFSG.Quasithin.R3c3.two_le_pRank_three_is3D4 (f := f) (X := X) h
  have hN : Nat.card X = ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  exact A318Exclusion.of_card hsimp hrank hN (l3Free_ordTrialityD4 hf)

theorem a318Exclusion_big_2f4 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 3 ≤ f)
    (h : ReeTitsModel X .twistedF4 2 f) : A318Exclusion X := by
  have hsimp := (CFSG.LieType.Simplicity.fam_2f4_simplicity X 2 f h).2
  have hrank := CFSG.Quasithin.R3c3.two_le_pRank_three_is2F4 (f := f) (X := X) h
  have hN : Nat.card X = ordTwistedF4 (2 ^ f) :=
    CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h
  exact A318Exclusion.of_card hsimp hrank hN (l3Free_ordTwistedF4 hf)

end CFSG.Quasithin.S1421QA20

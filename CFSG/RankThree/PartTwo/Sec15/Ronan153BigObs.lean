module

public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Ronan152Six153Core
public import CFSG.RankThree.PartTwo.Sec15.ThmDK148Front
public import CFSG.RankThree.PartTwo.Sec15.ThmDK148Chain
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly3
public import CFSG.RankThree.PartTwo.Sec15.ThmCM2Mult
public import CFSG.RankThree.PartTwo.Sec15.F153L3KFus
import CFSG.RankThree.PartTwo.Sec15.Ronan152SixHelpers

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan153Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem obsAt_of_big (h149 : Sec16.Item149S14) (hR : Sec15R G A c L)
    (h152 : Item152Big A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hYb : Big152 Y) (htypes : TwinTypesAt A Y) : ObsAt A Y := by
  intro S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hR.toSec14Std
  obtain ⟨hNX, hYX, -, hX2⟩ := facts153 h (h149 G A c L h) hY
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX2
  have hNXle : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hSX : S ≤ n155 A Y := hS.prop.1.2
  by_cases hE : HasFaithfulE9 Y
  · have hYA : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) :=
      sup_le Subgroup.le_normalizer hY.prop.1.1.2
    have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
      ⟨hM, fun x hx => hle (hNXle (hNX (hYA hx)))⟩
    have hMY : M ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (Ronan152Six.map_conj_eq_of_hasFaithfulE9_big h h152 hY hYb hE hMm ht)
    exact hSX.trans ((hNXle.trans hle).trans hMY)
  by_cases hNY : n155 A Y ≤ Subgroup.normalizer (Y : Set G)
  · exact hSX.trans hNY
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec14.le_normalizer_oPrimeResidualOf
      (Sec14.le_normalizer_delta (Subgroup.normalizer (Y : Set G)))
  have hYA : Y ⊔ A ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (hYX.trans Subgroup.le_normalizer) hAX
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (hNXle (hYA hx))⟩
  have hMY : ¬ M ≤ Subgroup.normalizer (Y : Set G) := fun hMY =>
    hNY ((hNXle.trans hle).trans hMY)
  have hdisj : ¬ 3 ∣ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) := by
    rcases htypes hE M hMm hMY with ⟨⟨e⟩⟩ | h6
    · exact Or.inl (F153Obs.not_dvd_three_card_center_of_alt5 e)
    · exact Or.inr h6
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    (Sec14.mem_scriptQ_iff.mp hS.prop.1.1).2.1
  exact F153Obs.theoremA881 G A c L hR Y hY.prop hdisj S hSX hAS
    (F153Obs.coprime_card_three_of_isPi_two hS.prop.2)

section Certs


theorem pCoreOf_sup_le_of_obsAt
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142c : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS14) (hR : Sec15R G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hobs : ObsAt A Y) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2)) :
    CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S := by
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := hobs S hS
  refine Ronan152Six.pCoreOf_sup_le_of_mem_scriptQ hR h146 hY hS hSY ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := CFSG.Open.pCoreOf 2 (Y ⊔ S) with hT
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    (Sec14.le_normalizer_sup hAY hAS).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hST : S ≤ Subgroup.normalizer (T : Set G) :=
    (le_sup_right : S ≤ Y ⊔ S).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTS2 : IsPGroup 2 ↥(S ⊔ T) := IsPGroup.to_sup_of_normal_right' hS2 hT2 hST
  have hP2 : IsPGroup 2 ↥((T ⊔ S) ⊓ Y) := hTS2.to_le (by rw [sup_comm]; exact inf_le_left)
  have hAP : A ≤ Subgroup.normalizer (((T ⊔ S) ⊓ Y : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (Sec14.le_normalizer_sup hAT hAS) hAY
  exact ThmD.mem_scriptQ_of_two_subgroup' hbot h148 h142c h143 h146
    (ThmC.pCoreOf_mem_scriptQ_of_scriptY0 ThmC.kFactM2_of_certificates h148 h142c h146 h1444
      hbot)
    (ThmD.step148FourKFact'_of_steps (step148YB_of_shape step148YBShape_holds)
        Ronan148M.step148HJ_holds Ronan148C.step148Core_holds Ronan148M.step148Point_holds
        Ronan148M.step148KType_holds Ronan148M.step148Lift_holds Ronan148M.step148D4_holds h148 h134
        h48)
    (ThmD.step153D3_of_inputs ThmD.a7CentralizerThreeCycle_holds h142c)
    (ThmD.step153D4_of_inputs F153L3K.l3FieldFusionK_holds h142c) G A c L hR Y
    (scriptY0Star_subset A (lB A) hY) _ inf_le_right hP2 hAP

end Certs

end CFSG.RankThree.PartTwo.Sec15.Ronan153Big

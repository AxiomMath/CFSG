module

public import CFSG.RankThree.PartTwo.Sec15.ThmDFront
public import CFSG.RankThree.PartTwo.Sec15.ThmDA10
public import CFSG.RankThree.PartTwo.Sec15.ThmDL3
public import CFSG.RankThree.PartTwo.Sec15.ThmDK7
public import CFSG.RankThree.PartTwo.Sec15.ThmCMain
public import CFSG.RankThree.PartTwo.Sec15.F153ObsR
public import CFSG.RankThree.PartTwo.Sec15.Gagen153Case7
public import CFSG.RankThree.PartTwo.Sec15.ThmDK148Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

section Front


theorem mem_scriptQ_of_two_subgroup'
    (hbot : Item145BotS14) (h148 : Item148R) (h142 : Concl142S14) (h143 : Concl143S14)
    (h146 : Item146S14)
    (hC : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A))
    (hP4 : Step148FourKFact') (hD3 : Step153D3) (hD4 : Step153D4) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P →
        A ≤ Subgroup.normalizer (P : Set G) → P ∈ scriptQ A (lB A) := by
  intro G _ _ A c L hR Y hY0 P hPY hP2 hAP
  have hS := hR.toSec14Std
  have hA : IsE27 A := hS.isE27
  have hAab : IsMulCommutative A := hR.isElemAbelian.1
  have hY4 : Y ∈ scriptY4 A (lB A) := hY0.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY4.1.2
  have hbot' : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ := hbot G A c L hS
  have hYΔ : Y = deltaZero A (lB A) Y := rank3II_15_1_lB hA hbot' hY4
  have hV := hC G A c L hR Y hY0
  have hP3 := not_three_dvd_card_of_isPGroup_two hP2
  by_cases hcen : CentralizesQuot A Y
  · obtain ⟨a, haA, ha1, hc⟩ := hcen
    exact mem_scriptQ_of_centralizes hA (h142 G A c L hS) (h143 G A c L hS) (h146 G A c L hS)
      hY4.2.2.1 hAY hV haA ha1 hc hPY hP3 hAP
  · rcases cases148_split (h148 G A c L hR) hAab hY4 hYΔ with
      ⟨a, haA, ha1, hYa⟩ | ⟨h10, hL7, hW⟩ | h5
    · exact (hcen ⟨a, haA, ha1, (ThmC.lemma7_centralizes hY0 haA hYa).1⟩).elim
    · exact hD3 G A c L hR Y hY0 hV hcen h10 (hP4 G A c L hR Y hY0 hYΔ hcen h10 hL7 hW) P hPY hP2
        hAP
    · exact hD4 G A c L hR Y hY0 hYΔ hV h5 P hPY hP2 hAP

theorem step153PushCoreR_of_faithful' (hobs : Claim153ObsR)
    (hbot : Item145BotS14) (h148 : Item148R) (h142 : Concl142S14) (h143 : Concl143S14)
    (h146 : Item146S14)
    (hC : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A))
    (hP4 : Step148FourKFact') (hD3 : Step153D3) (hD4 : Step153D4) : Step153PushCoreR := by
  refine step153PushCoreR_of_P hobs h146 fun G _ _ A c L hR Y hY S hS hSY => ?_
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
  exact mem_scriptQ_of_two_subgroup' hbot h148 h142 h143 h146 hC hP4 hD3 hD4 G A c L hR Y
    (scriptY0Star_subset A (lB A) hY) _ inf_le_right hP2 hAP

end Front

section Main


theorem step153PushCoreR_of_inputs_v2 (hM2 : ThmC.KFactM2) (h148 : Sec14.Item148R)
    (h149 : Sec16.Item149S14) (h152 : Item152R) (h142 : Sec14.Concl142S14)
    (h143 : Sec14.Concl143S14) (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14)
    (hbot : Sec14.Item145BotS14) (hL3 : L3FieldFusionK) (hP4 : Step148FourKFact') :
    Step153PushCoreR :=
  step153PushCoreR_of_faithful'
    (F153Obs.claim153ObsR_of F153Obs.theoremA881
      (claim153TwinTypes_of h148 h149 h152 (claim153TwinCase7_of_item148R h148)) h149 h152)
    hbot h148 h142 h143 h146 (ThmC.pCoreOf_mem_scriptQ_of_scriptY0 hM2 h148 h142 h146 h1444 hbot)
    hP4 (step153D3_of_inputs a7CentralizerThreeCycle_holds h142) (step153D4_of_inputs hL3 h142)

end Main

end CFSG.RankThree.PartTwo.Sec15.ThmD

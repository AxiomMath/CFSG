module

public import CFSG.RankThree.PartTwo.Sec15.ThmDFront
public import CFSG.RankThree.PartTwo.Sec15.ThmDA10
public import CFSG.RankThree.PartTwo.Sec15.ThmDL3
public import CFSG.RankThree.PartTwo.Sec15.ThmDK7
public import CFSG.RankThree.PartTwo.Sec15.ThmCMain

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan152Six

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem pCoreOf_sup_le_of_mem_scriptQ (hR : Sec15R G A c L) (h146 : Item146S14)
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2))
    (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hPQ : (CFSG.Open.pCoreOf 2 (Y ⊔ S) ⊔ S) ⊓ Y ∈ scriptQ A (lB A)) :
    CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := CFSG.Open.pCoreOf 2 (Y ⊔ S) with hT
  set P := (T ⊔ S) ⊓ Y with hPdef
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hSN : S ≤ n155 A Y := hS.prop.1.2
  have hST : S ≤ Subgroup.normalizer (T : Set G) :=
    (le_sup_right : S ≤ Y ⊔ S).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTS2 : IsPGroup 2 ↥(S ⊔ T) := IsPGroup.to_sup_of_normal_right' hS2 hT2 hST
  have hTS : T ⊔ S = S ⊔ T := sup_comm _ _
  have hTle : T ≤ Y ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hPS : T ⊔ S ≤ P ⊔ S := by
    intro x hx
    have hxYS : x ∈ Y ⊔ S := sup_le hTle le_sup_right hx
    have hxm : x ∈ ((Y : Set G) * (S : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y S hSY]
      exact hxYS
    obtain ⟨y, hy, s, hs, rfl⟩ := hxm
    have hyTS : y ∈ T ⊔ S := by
      have := (T ⊔ S).mul_mem hx ((T ⊔ S).inv_mem (Subgroup.mem_sup_right hs))
      simpa using this
    exact (P ⊔ S).mul_mem (Subgroup.mem_sup_left (show y ∈ P from ⟨hyTS, hy⟩))
      (Subgroup.mem_sup_right hs)
  have hSP : S ≤ Subgroup.normalizer (P : Set G) :=
    Late.le_normalizer_inf ((le_sup_right : S ≤ T ⊔ S).trans Subgroup.le_normalizer) hSY
  have hsup : S ⊔ P ∈ scriptQ A (lB A) :=
    Sec14.sup_mem_scriptQ_of_item146 hR.toSec14Std.isE27 (h146 G A c L hR.toSec14Std)
      hS.prop.1.1 hPQ hSP
  have hYN : Y ≤ n155 A Y :=
    (le_oPrimeResidualOf_delta hY.prop.1 Subgroup.le_normalizer).trans Subgroup.le_normalizer
  have hPN : P ≤ n155 A Y := inf_le_right.trans hYN
  have hSPle : S ⊔ P ≤ S ⊔ T := sup_le le_sup_left (inf_le_left.trans (by rw [← hTS]))
  have h2 : IsPGroup 2 ↥(S ⊔ P) := hTS2.to_le hSPle
  have hmem : S ⊔ P ∈ scriptQPi A (lB A) (n155 A Y) (piOf 2) :=
    ⟨⟨hsup, sup_le hSN hPN⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr h2⟩
  have hPS' : S ⊔ P ≤ S := hS.2 hmem le_sup_left
  exact (le_sup_left.trans hPS).trans (sup_le (le_sup_right.trans hPS') le_rfl)

section Certs


theorem pCoreOf_sup_le_of_le_normalizer (hM2 : ThmC.KFactM2) (h148 : Item148R)
    (h142 : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS14) (hL3 : ThmD.L3FieldFusionK) (hP4 : ThmD.Step148FourKFact)
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2))
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) :
    CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S := by
  refine pCoreOf_sup_le_of_mem_scriptQ hR h146 hY hS hSY ?_
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
  exact ThmD.mem_scriptQ_of_two_subgroup hbot h148 h142 h143 h146
    (ThmC.pCoreOf_mem_scriptQ_of_scriptY0 hM2 h148 h142 h146 h1444 hbot) hP4
    (ThmD.step153D3_of_inputs ThmD.a7CentralizerThreeCycle_holds h142)
    (ThmD.step153D4_of_inputs hL3 h142) G A c L hR Y (scriptY0Star_subset A (lB A) hY) _
    inf_le_right hP2 hAP

end Certs

end CFSG.RankThree.PartTwo.Sec15.Ronan152Six

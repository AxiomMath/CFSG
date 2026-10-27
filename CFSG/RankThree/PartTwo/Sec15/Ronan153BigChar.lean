module

public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigObs
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigCharLeaves
public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofLink
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofM12
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannMain
import CFSG.RankThree.PartTwo.Sec15.Item155Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan153Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem exists_block_at (h149 : Sec16.Item149S14) (hR : Sec15R G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (htw : TwinAt A Y) {H : Subgroup G}
    (hHN : H ≤ n155 A Y)
    (hsub : (((oResidual 2 ↥H).map H.subtype).subgroupOf (n155 A Y)).IsSubnormal)
    (hb : IsScriptLBlock ⊤ (oResidual 2 ↥H)) :
    ∃ M L' : Subgroup G, CFSG.IsMaximalTwoLocal M ∧ IsScriptLBlock M L' :=
  ⟨n155 A Y, _,
    (n155_mem_maximalTwoLocalsContaining_of_twinAt hR.toSec14Std (h149 G A c L hR.toSec14Std)
      hY htw).1,
    Proof153Block.isScriptLBlock_map_subtype hb hHN hsub⟩

section Certs


theorem concl153Push_at
    (h149 : Sec16.Item149S14) (h148 : Item148R) (h134 : Item134)
    (h135 : Item135) (h137 : Item137) (h142 : Item142AllS14) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h142c : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14)
    (h1444 : Item1444S14) (hbot : Item145BotS14) (h148HJ : Item148HJS14)
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (htw : TwinAt A Y)
    (hobs : ObsAt A Y) {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2))
    (hno : ¬ CharNormal153 Y S) : Concl153Push A Y S := by
  have hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y :=
    generalizedFitting_eq_of_twinAt hR.toSec14Std (h149 G A c L hR.toSec14Std) hY htw
  have hO := pCoreOf_sup_le_of_obsAt h148 h134 h48 h142c h143 h146 h1444 hbot hR hY hobs hS
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hS1 : S ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq] at hO
    exact hY.prop.2.2 (le_bot_iff.mp hO)
  have hFF : FF153 Y S :=
    ⟨hO, fun hJ => hno (Push153.charNormal153_of_thompsonJ_le hS2 hS1 hO hJ)⟩
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := hobs S hS
  by_cases hT : Listed315 (↥Y ⧸ CFSG.pCore 2 ↥Y)
  · exact Or.inl (exists_hyp315_of_listed_at h149 hR hY hF hS hSY hT
      (step153PushListedR_of_item148R h148 h134 h48 G A c L hR Y hY S hS hno hFF hSY hT))
  by_cases hJ2 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact concl153Push_of_j2_at hR hY hF hS hno hFF hSY hJ2
  by_cases hL : IsL3Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y)
  · exact concl153Push_of_l3_at h148 h134 h48 h148HJ hR hY hF hS hno hFF hSY hL
  by_cases hM : IsM22Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y)
  · exact concl153Push_of_m22_at hR hY hF hS hno hFF hSY hM
  by_cases hM' : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12)
  · exact step153PushM12R_of_item157 h137 h142 h134 h135 h48 h415 h148 G A c L hR Y hY S hS hno
      hFF hSY hM'
  by_cases hA : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))
  · exact concl153Push_of_a10_at hR hY hF hS hno hFF hSY hA
  exact concl153Push_of_rest_at h148 h134 h48 hR hY hF hS hno hFF hSY hT
    (not_nonempty_iff.mp hJ2) hL hM (not_nonempty_iff.mp hM') (not_nonempty_iff.mp hA)

theorem charAt_of
    (h316 : Sec19.Item316) (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h134 : Item134) (h135 : Item135) (h137 : Item137) (h142 : Item142AllS14)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h142c : Concl142S14) (h143 : Concl143S14)
    (h146 : Item146S14) (h1444 : Item1444S14) (hbot : Item145BotS14) (h148HJ : Item148HJS14)
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (htw : TwinAt A Y)
    (hobs : ObsAt A Y) : CharAt A Y := by
  intro S hS
  by_contra hno
  rcases concl153Push_at h149 h148 h134 h135 h137 h142 h48 h415 h142c h143 h146 h1444 hbot
      h148HJ hR hY htw hobs hS hno with ⟨H, hYSH, hHN, hsub, hyp⟩ | ⟨M, L', hM, hL'⟩
  · rcases exists_char_normal_of_hyp315 item3_15_holds hyp with ⟨C, hC1, hCS, hCc, hHC⟩ | hb
    · exact hno ⟨C, hC1, hCS, hCc, hYSH.trans hHC⟩
    · obtain ⟨M, L', hM, hL'⟩ := exists_block_at h149 hR hY htw hHN hsub hb
      exact false_of_isScriptLBlock_of_sec13Data h316 hR.toSec13Data hM hL'
  · exact false_of_isScriptLBlock_of_sec13Data h316 hR.toSec13Data hM hL'

end Certs

end CFSG.RankThree.PartTwo.Sec15.Ronan153Big

module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofList
public import CFSG.RankThree.PartTwo.KFacts.KP4Signal
import CFSG.RankThree.PartTwo.Sec16.Item1611Res2ProofModel
import CFSG.RankThree.PartTwo.Sec16.Item1611Res2ProofPoint
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGen
import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof1611Res2M22

open KFacts.KP4

theorem two_subgroup_facts :
    (∀ X : Subgroup G22, IsPGroup 2 X → P0 ≤ Subgroup.normalizer (X : Set G22) → V 0 ≤ X →
      X ⊓ Subgroup.centralizer ({lineE 2} : Set G22) = ⊥) ∧
    V 2 ⊓ Subgroup.centralizer ({lineE 2} : Set G22) ≠ ⊥ := by
  refine ⟨fun X hX2 hPX hVX => ?_, fun hbot => ?_⟩
  · have h3 := Proof1611Res2.not_three_dvd_card_of_isPGroup_two hX2
    rcases inf_centralizer_cases h3 hPX 2 with h | h
    · exact h
    · exfalso
      have hV2 : V 2 ≤ X := h ▸ inf_le_left
      have hpair : V (pairFst 0) ⊔ V (pairSnd 0) ≤ X := sup_le hVX hV2
      exact h3 ((three_dvd_card_pair 0).trans (Subgroup.card_dvd_of_le hpair))
  · rw [inf_eq_left.mpr (V_le_centralizer 2)] at hbot
    have h4 := card_V 2
    rw [hbot, Subgroup.card_bot] at h4
    omega

end Proof1611Res2M22

open Proof1611Res2M22 KFacts.KP4 in
theorem ks1611M22NotTrans :
    KS1611M22NotTrans := by
  intro G _ _ A c L h hM hAab hcA h142
  have : (ker142 A (lB A) c).Normal := ker142_normal hAab hcA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS14 := h.toSec14Std
  have hD := h.toSec13Data
  have hX := KFacts.KS14.ks18A7M22 (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Or.inr hM)
  obtain ⟨-, h9, hAc⟩ := Proof1611Res2.point_facts_of_inner_aut hD hX.2.1
    (fun σ hσ => hX.2.2.1 σ ⟨1, by rw [pow_one]; exact hσ⟩)
  obtain ⟨ψ, hψ⟩ := exists_equiv_P0 hM (Res5Gen.card_image_inf hS14 h9)
  have hφ : (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map ψ.symm.toMonoidHom = P0 := by
    rw [← hψ]
    exact Sec4.Sporadic.map_symm_map ψ P0
  have hLK := Proof1611Res2.le_k142_of_item142 hS14 h142 (by
    obtain ⟨φ⟩ := hM
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
    norm_num)
  obtain ⟨h1, h2⟩ := two_subgroup_facts
  exact Proof1611Res2.not_transOn_of_model sporadicModels131 hS14 hLK
    (fun Q hQ => (h142 Q hQ).1) hAc ψ.symm hφ (lineE_mem_P0 2)
    (IsPGroup.of_card (n := 2) (by rw [card_V]; norm_num)) (P0_le_normalizer_V 0)
    (IsPGroup.of_card (n := 2) (by rw [card_V]; norm_num)) (P0_le_normalizer_V 2) h1 h2

end CFSG.RankThree.PartTwo.Sec16

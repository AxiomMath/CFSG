module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofList
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesA7
import CFSG.RankThree.PartTwo.Sec16.Item1611Res2ProofModel
import CFSG.RankThree.PartTwo.Sec16.Item1611Res2ProofPoint
import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof1611Res2A7

open Equiv KFacts.KP2 Res5TypesA7

theorem vOneF_one_ne : ∀ m : Fin 4, vOneF 1 ≠ vTwoF m := by
  decide +kernel

theorem two_subgroup_facts :
    (∀ X : Subgroup ↥(alternatingGroup (Fin 7)), IsPGroup 2 X →
      P7 ≤ Subgroup.normalizer (X : Set ↥(alternatingGroup (Fin 7))) → V1 ≤ X →
      X ⊓ Subgroup.centralizer ({c2} : Set ↥(alternatingGroup (Fin 7))) = ⊥) ∧
    V2 ⊓ Subgroup.centralizer ({c2} : Set ↥(alternatingGroup (Fin 7))) ≠ ⊥ := by
  have hV1C : V1 ⊓ Subgroup.centralizer ({c2} : Set ↥(alternatingGroup (Fin 7))) = ⊥ := by
    rw [eq_bot_iff]
    intro v hvI
    obtain ⟨hv, hvC⟩ := Subgroup.mem_inf.mp hvI
    rw [Subgroup.mem_bot]
    obtain ⟨m, hm⟩ := (Subgroup.mem_subgroupOf.mp hv : (v : Perm (Fin 7)) ∈ vOne)
    have hc : (v : Perm (Fin 7)) * cTwo = cTwo * v :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hvC)
    by_cases hm0 : m = 0
    · subst hm0
      apply Subtype.ext
      rw [hm]
      exact vOne_facts.2.2.2.2.2.2.1
    · exact absurd (hm ▸ hc) (vOneF_not_commute m hm0)
  refine ⟨fun X hX2 hPX hVX => ?_, fun hbot => ?_⟩
  · rcases le_V_of_invariant (Proof1611Res2.not_three_dvd_card_of_isPGroup_two hX2) hPX with
      h | h
    · exact eq_bot_iff.mpr ((inf_le_inf_right _ h).trans hV1C.le)
    · exfalso
      have h1 : v1 1 ∈ V2 := h (hVX ((mem_V1_iff _).mpr (Or.inr (Or.inl rfl))))
      obtain ⟨m, hm⟩ := (Subgroup.mem_subgroupOf.mp h1 : ((v1 1 : ↥(alternatingGroup (Fin 7))) :
        Perm (Fin 7)) ∈ vTwo)
      exact vOneF_one_ne m hm
  · have hV2C : V2 ≤ Subgroup.centralizer ({c2} : Set ↥(alternatingGroup (Fin 7))) := by
      intro v hv
      obtain ⟨m, hm⟩ := (Subgroup.mem_subgroupOf.mp hv : (v : Perm (Fin 7)) ∈ vTwo)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change (v : Perm (Fin 7)) * cTwo = cTwo * v
      rw [hm]
      exact (vTwoF_spec m).1
    rw [inf_eq_left.mpr hV2C] at hbot
    have h4 := V_facts.2.1
    rw [hbot, Subgroup.card_bot] at h4
    omega

end Proof1611Res2A7

open Proof1611Res2A7 KFacts.KP2 Res5TypesA7 in
theorem ks1611A7NotTrans :
    KS1611A7NotTrans := by
  intro G _ _ A c L h hA7 hAab hcA h142
  have : (ker142 A (lB A) c).Normal := ker142_normal hAab hcA
  have hS14 := h.toSec14Std
  have hD := h.toSec13Data
  have hX := KFacts.KS14.ks18A7M22 (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Or.inl hA7)
  obtain ⟨-, h9, hAc⟩ := Proof1611Res2.point_facts_of_inner_aut hD hX.2.1
    (fun σ hσ => hX.2.2.1 σ ⟨1, by rw [pow_one]; exact hσ⟩)
  obtain ⟨φ⟩ := hA7
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hfac : (Nat.card ↥(alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [hcard]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 2520 = 3 ^ 2 * 280 by norm_num) (by norm_num)
  obtain ⟨φ', hφ'⟩ := Res5Types.exists_equiv_map_eq φ card_P7 (Res5Gen.card_image_inf hS14 h9)
    hfac
  have hLK := Proof1611Res2.le_k142_of_item142 hS14 h142
    (by rw [Nat.card_congr φ.toEquiv, hcard]; norm_num)
  obtain ⟨h1, h2⟩ := two_subgroup_facts
  obtain ⟨hV1, hV2, hN1, hN2⟩ := V_facts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Proof1611Res2.not_transOn_of_model sporadicModels131 hS14 hLK
    (fun Q hQ => (h142 Q hQ).1) hAc φ' hφ' c2_mem_P7
    (IsPGroup.of_card (n := 2) (by rw [hV1]; norm_num)) hN1
    (IsPGroup.of_card (n := 2) (by rw [hV2]; norm_num)) hN2 h1 h2

end CFSG.RankThree.PartTwo.Sec16

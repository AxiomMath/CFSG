module

public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface2
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofNormal
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.RankThree.PartTwo.Sec3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemTwo_of_isElemAbelian {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) :
    IsElemTwo A := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · have h := hA.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩
    exact congrArg Subtype.val h
  · rw [← pow_two]
    exact hA.2 a ha

omit [Finite G] in
theorem isElemAbelian_of_isElemTwo {A : Subgroup G} (hA : IsElemTwo A) :
    CFSG.Open.IsElemAbelian 2 A := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (hA.1 a a.2 b b.2)
  · rw [pow_two]
    exact hA.2 x hx

omit [Finite G] in
theorem mem_centerOf_iff {J : Subgroup G} {x : G} :
    x ∈ centerOf J ↔ x ∈ J ∧ ∀ y ∈ J, x * y = y * x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun y hy => ?_⟩
    have h := Subgroup.mem_center_iff.mp hc ⟨y, hy⟩
    exact (congrArg Subtype.val h).symm
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hc g.1 g.2).symm

omit [Finite G] in
theorem omegaOneZ_eq_omegaG (J : Subgroup G) : omegaOneZ J = omegaG J := by
  have hset : {x : G | x ∈ centerOf J ∧ x ^ 2 = 1} = (omegaG J : Set G) := by
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_omegaG, mem_centerOf_iff]
    constructor
    · rintro ⟨⟨hxJ, hc⟩, hx2⟩
      exact ⟨hxJ, hc, by rw [← pow_two]; exact hx2⟩
    · rintro ⟨hxJ, hc, hx2⟩
      exact ⟨⟨hxJ, hc⟩, by rw [pow_two]; exact hx2⟩
  unfold omegaOneZ
  rw [hset, Subgroup.closure_eq]

theorem jOf_eq_jG_zero (S : Subgroup G) : jOf S = jG S 0 := by
  have hm : CFSG.pRank 2 S = CFSG.Open.pRank 2 S := CFSG.SectionRank.pRank_coe_eq_openPRank 2 S
  apply le_antisymm
  · unfold jOf
    refine iSup₂_le fun E hE => ?_
    obtain ⟨hES, hEab, hcard⟩ := hE
    have hmem : E ∈ famG S 0 :=
      mem_famG.mpr ⟨hES, isElemTwo_of_isElemAbelian hEab, by rw [Nat.sub_zero, hm]; exact hcard⟩
    exact le_sSup hmem
  · unfold jG jOf
    refine sSup_le fun A hA => ?_
    obtain ⟨hAS, hA2, hcard⟩ := mem_famG.mp hA
    rw [Nat.sub_zero, hm] at hcard
    exact le_iSup₂_of_le A ⟨hAS, isElemAbelian_of_isElemTwo hA2, hcard⟩ le_rfl

theorem jOneOf_eq_jG_one {S : Subgroup G} (hS : 2 ≤ CFSG.pRank 2 S) :
    jOneOf S = jG S 1 := by
  have hm : CFSG.pRank 2 S = CFSG.Open.pRank 2 S := CFSG.SectionRank.pRank_coe_eq_openPRank 2 S
  have h1 : 1 ≤ CFSG.pRank 2 S - 1 := by omega
  apply le_antisymm
  · unfold jOneOf
    refine iSup₂_le fun E hE => ?_
    obtain ⟨hES, hEab, hcard⟩ := hE
    have hcard' : 2 ^ (CFSG.pRank 2 S - 1) ≤ Nat.card E := by rw [hm]; exact hcard
    exact (Item181ThreeProof.le_pAt_of_card (le_refl S) hES (isElemTwo_of_isElemAbelian hEab) h1
      hcard').trans (Item181ThreeProof.pAt_le_jG S S 1)
  · unfold jG jOneOf
    refine sSup_le fun A hA => ?_
    obtain ⟨hAS, hA2, hcard⟩ := mem_famG.mp hA
    rw [hm] at hcard
    exact le_iSup₂_of_le A ⟨hAS, isElemAbelian_of_isElemTwo hA2, hcard.symm.le⟩ le_rfl

theorem tripleOf_zero_eq (S : Subgroup G) : tripleOf S 0 = fourChar S 1 := by
  rw [Item181ThreeProof.fourChar_one]
  show jOf S = jG S 0
  exact jOf_eq_jG_zero S

theorem tripleOf_two_eq (S : Subgroup G) : tripleOf S 2 = fourChar S 0 := by
  rw [Item181ThreeProof.fourChar_zero]
  show omegaOneZ S = omegaG S
  exact omegaOneZ_eq_omegaG S

theorem tripleOf_one_eq {S : Subgroup G} (hS : 2 ≤ CFSG.pRank 2 S) :
    tripleOf S 1 = fourChar S 2 := by
  rw [Item181ThreeProof.fourChar_two, ← jOneOf_eq_jG_one hS]
  show omegaOneZ (jOneOf S) = omegaG (jOneOf S)
  exact omegaOneZ_eq_omegaG (jOneOf S)

theorem fourChar_zero_eq_one {S : Subgroup G} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hS : CFSG.pRank 2 S ≤ 1) : fourChar S 0 = fourChar S 1 := by
  have hj1 : jG S 1 = ⊥ := Item181ThreeProof.jG_eq_bot_of_pRank_sub_eq_zero (by omega)
  have hE : omegaG (jG S 1) = ⊥ := by
    rw [hj1]
    exact eq_bot_iff.mpr ((omegaG_le ⊥).trans le_rfl)
  rw [Item181ThreeProof.fourChar_zero, Item181ThreeProof.fourChar_one]
  exact CFSG.RankThree.PartTwo.Sec20.Res5.omegaG_eq_jG_zero_of_omegaG_jG_one_eq_bot hS2 hS1 hE

theorem normalizer_le_normalizer_fourChar (S : Subgroup G) (k : Fin 4) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S k : Set G) := by
  have h0 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S 0 : Set G) := by
    rw [Item181ThreeProof.fourChar_zero]
    exact Item181ThreeProof.normalizer_le_normalizer_omegaG S
  have h1 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S 1 : Set G) := by
    rw [Item181ThreeProof.fourChar_one]
    exact Item181ThreeProof.normalizer_le_normalizer_jG S 0
  have h2 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S 2 : Set G) := by
    rw [Item181ThreeProof.fourChar_two]
    exact (Item181ThreeProof.normalizer_le_normalizer_jG S 1).trans
      (Item181ThreeProof.normalizer_le_normalizer_omegaG (jG S 1))
  have h3 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S 3 : Set G) := by
    rw [Item181ThreeProof.fourChar_three]
    exact (Item181ThreeProof.normalizer_le_normalizer_jG S 2).trans
      (Item181ThreeProof.normalizer_le_normalizer_omegaG (jG S 2))
  fin_cases k
  exacts [h0, h1, h2, h3]

end CFSG.RankThree.PartTwo.Sec18.Item187Proof

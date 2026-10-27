module

public import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProof
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] noncomputable def Claim1411NonsolvWPointR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y →
          TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            (Subgroup.zpowers a ∈ omegaA A ∨
              delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
                pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
                  pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) →
            IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T

@[expose] noncomputable def Claim1411NonsolvXPointR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      (∀ a : G, Subgroup.zpowers a ∈ omegaA A →
          TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G))) →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y → TransOn A (lB A) (xA A) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (xA A ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            (Subgroup.zpowers a ∈ omegaA A ∨
              delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
                pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
                  pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) →
            IsConjIn (xA A ⊓ Y) S T

namespace Proof1413Res4

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_of_delta_eq {A : Subgroup G} {a : G} (ha : a ∈ A) {Y : Subgroup G}
    (hYΔ : Y = delta A (lB A) Y) (hYa : Y ≤ Subgroup.centralizer ({a} : Set G))
    (hΔ : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    ¬ 3 ∣ Nat.card Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Y ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    rw [← hΔ, hYΔ]
    exact delta_mono hYa
  rw [sup_comm] at hle
  have hXa : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))).trans
      (le_normalizer_pPrimeCoreOf 3 _)
  have h3' : ∀ Z : Subgroup G, IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 Z) := fun Z =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Z))
  have hK := (isPiSubgroup_piCompl_iff Nat.prime_three _).mp
    (isPiSubgroup_piCompl_sup (h3' _) (h3' _) hXa)
  exact fun h3 => hK (h3.trans (Subgroup.card_dvd_of_le hle))

theorem exists_point_of_ne {A Y S T : Subgroup G} (hA : IsE27 A)
    (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2)) (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hST : S ≠ T) :
    ∃ a ∈ A, a ≠ 1 ∧ ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T ∧
      ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop
  have hcop : ∀ U : Subgroup G, IsPGroup 2 U → Nat.Coprime 3 (Nat.card U) := by
    intro U hU
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  refine exists_inf_centralizer_not_le hA (fun h => hST ?_) (fun h => hST ?_)
    hS.prop.1.1.1.2.2 hT.prop.1.1.1.2.2 (hcop S hS2) (hcop T hT2)
  · exact hS.eq_of_le hT.prop (h.trans inf_le_right)
  · exact (hT.eq_of_le hS.prop (h.trans inf_le_left)).symm

end Proof1413Res4

open Proof1413Res4 in
theorem claim1411NonsolvWCentR_of_point (h : Claim1411NonsolvWPointR) :
    Claim1411NonsolvWCentR := by
  intro G _ _ A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres
  by_cases hST : S = T
  · subst hST
    exact isConjIn_refl _ _
  obtain ⟨a, haA, ha1, haS, haT⟩ := exists_point_of_ne hR.toSec14Std.isE27 hS hT hST
  by_cases hpt : Subgroup.zpowers a ∈ omegaA A ∨
      delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  · exact h G A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt
  · push Not at hpt
    exact absurd h3 (not_three_dvd_of_delta_eq haA hYΔ (hres a haA ha1 haS haT) hpt.2)

open Proof1413Res4 in
theorem claim1411NonsolvXCentR_of_point (h : Claim1411NonsolvXPointR) :
    Claim1411NonsolvXCentR := by
  intro G _ _ A c L hR hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres
  by_cases hST : S = T
  · subst hST
    exact isConjIn_refl _ _
  obtain ⟨a, haA, ha1, haS, haT⟩ := exists_point_of_ne hR.toSec14Std.isE27 hS hT hST
  by_cases hpt : Subgroup.zpowers a ∈ omegaA A ∨
      delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  · exact h G A c L hR hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt
  · push Not at hpt
    exact absurd h3 (not_three_dvd_of_delta_eq haA hYΔ (hres a haA ha1 haS haT) hpt.2)

theorem claim1411NonsolvWR_of_point (h146 : Item146S14) (hbot : Item145BotS14)
    (h : Claim1411NonsolvWPointR) : Claim1411NonsolvWR :=
  claim1411NonsolvWR_of h146 hbot (claim1411NonsolvWCentR_of_point h)

theorem claim1411NonsolvXR_of_point (h146 : Item146S14) (hbot : Item145BotS14)
    (h : Claim1411NonsolvXPointR) : Claim1411NonsolvXR :=
  claim1411NonsolvXR_of h146 hbot (claim1411NonsolvXCentR_of_point h)

end CFSG.RankThree.PartTwo.Sec14

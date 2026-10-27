module

import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

section Induction

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem transOn_of_cent (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {V : Subgroup G}
    (hVA : V ≤ Subgroup.normalizer (A : Set G)) (hXV : xA A ≤ V)
    (hcent : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
      ¬ Group.IsSolvable ↥Y → 3 ∣ Nat.card Y →
      (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
      (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y → TransOn A (lB A) V Y') →
      ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
        Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
        (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
            IsConjIn (V ⊓ Y) S' T') →
        (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
          ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
        IsConjIn (V ⊓ Y) S T) :
    ∀ Y ∈ scriptY A, TransOn A (lB A) V Y := by
  have hA : IsE27 A := h.isE27
  have hnat : IsNaturalFamily A (lB A) := isNaturalFamily_lB A
  suffices H : ∀ n : ℕ, ∀ Y ∈ scriptY A, Nat.card Y = n → TransOn A (lB A) V Y from
    fun Y hY => H _ Y hY rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hY hYn
  have hIHc : ∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y → TransOn A (lB A) V Y' :=
    fun Y' hY' hlt => ih _ (hYn ▸ hlt) Y' hY' rfl
  have hIH : ∀ Y' ∈ scriptY A, Y' < Y → TransOn A (lB A) V Y' := fun Y' hY' hlt =>
    hIHc Y' hY' (Subgroup.card_lt_of_lt hlt)
  by_cases hYΔ : Y = delta A (lB A) Y
  · by_cases hs : Group.IsSolvable ↥Y
    · exact transOn_mono hXV (transOn_of_isSolvable_std h h146 hbot hYΔ hY hs)
    by_cases h3 : 3 ∣ Nat.card Y
    · have hBc : ∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥ :=
        fun B hB hYB hLB => not_three_dvd_delta_of_le_centralizer hB hLB hYB (by
          rw [← hYΔ]
          exact h3)
      exact transOn_of_residual hA hnat h146 hVA hY hIH (hcent Y hYΔ hY hs h3 hBc hIHc)
    · exact transOn_mono hXV (transOn_of_not_three_dvd hA h146 hbot hYΔ hY h3)
  ·
    have hlt : delta A (lB A) Y < Y := lt_of_le_of_ne (delta_le Y) (Ne.symm hYΔ)
    have hΔY : delta A (lB A) Y ∈ scriptY A :=
      ⟨fun htop => hY.1 (top_le_iff.mp (htop.symm.le.trans (delta_le Y))),
        le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩
    exact transOn_of_delta (hIH _ hΔY hlt)

theorem rank3II_14_11_2_of_cent (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hcent : (∀ a : G, Subgroup.zpowers a ∈ omegaA A →
        TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G))) →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
        ¬ Group.IsSolvable ↥Y → 3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y → TransOn A (lB A) (xA A) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (xA A ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          IsConjIn (xA A ⊓ Y) S T) :
    Item1411_2 A (lB A) := by
  intro hloc S hS T hT
  rw [inf_top_eq]
  exact rank3II_14_11_2_lB h (transOn_of_cent h h146 hbot
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)) le_rfl (hcent hloc)) hS hT

end Induction

@[expose] noncomputable def Claim1411NonsolvWCentR : Prop :=
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
          IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T

@[expose] noncomputable def Claim1411NonsolvXCentR : Prop :=
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
          IsConjIn (xA A ⊓ Y) S T

theorem claim1411NonsolvWR_of (h146 : Item146S14) (hbot : Item145BotS14)
    (hcent : Claim1411NonsolvWCentR) : Claim1411NonsolvWR := by
  intro G _ _ A c L hR Y _ hY _
  exact transOn_of_cent hR.toSec14Std (h146 G A c L hR.toSec14Std) (hbot G A c L hR.toSec14Std)
    le_rfl ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)) (hcent G A c L hR)
    Y hY

theorem claim1411NonsolvXR_of (h146 : Item146S14) (hbot : Item145BotS14)
    (hcent : Claim1411NonsolvXCentR) : Claim1411NonsolvXR := by
  intro G _ _ A c L hR hloc Y _ hY _
  exact transOn_of_cent hR.toSec14Std (h146 G A c L hR.toSec14Std) (hbot G A c L hR.toSec14Std)
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)) le_rfl
    (hcent G A c L hR hloc) Y hY

end CFSG.RankThree.PartTwo.Sec14

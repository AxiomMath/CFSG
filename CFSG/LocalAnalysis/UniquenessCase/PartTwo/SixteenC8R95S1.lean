module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem r95s_relIndex_split {H A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H)
    (hB : H ≤ normalizer (B : Set G)) :
    A.relIndex H = (A ⊔ B).relIndex H * (A ⊓ B).relIndex B := by
  have hAN : A ≤ normalizer (B : Set G) := hAH.trans hB
  have h1 := Subgroup.relIndex_mul_relIndex A (A ⊔ B) H le_sup_left (sup_le hAH hBH)
  have h2 : A.relIndex (A ⊔ B) = (A ⊓ B).relIndex B := by
    have hcard := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hAN
    have hA := Subgroup.relIndex_mul_card A (A ⊔ B)
    have hB' := Subgroup.relIndex_mul_card (A ⊓ B) B
    rw [inf_eq_left.mpr le_sup_left] at hA
    rw [inf_eq_left.mpr inf_le_right] at hB'
    have hkey : A.relIndex (A ⊔ B) * (Nat.card ↥A * Nat.card ↥(A ⊓ B)) =
        (A ⊓ B).relIndex B * (Nat.card ↥A * Nat.card ↥(A ⊓ B)) := by
      calc A.relIndex (A ⊔ B) * (Nat.card ↥A * Nat.card ↥(A ⊓ B))
          = (A.relIndex (A ⊔ B) * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by
            rw [mul_assoc]
        _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by rw [hA]
        _ = Nat.card ↥A * Nat.card ↥B := hcard
        _ = Nat.card ↥A * ((A ⊓ B).relIndex B * Nat.card ↥(A ⊓ B)) := by rw [hB']
        _ = (A ⊓ B).relIndex B * (Nat.card ↥A * Nat.card ↥(A ⊓ B)) := by ring
    exact Nat.mul_right_cancel (Nat.mul_pos Nat.card_pos Nat.card_pos) hkey
  rw [← h1, h2]
  exact mul_comm _ _

theorem r95s_sylow_of_odd_index {H I M : Subgroup G} (hIH : I ≤ H)
    (hHI : H ≤ normalizer (I : Set G)) (hI : ¬ 2 ∣ (I ⊓ M).relIndex I)
    (hB : ¬ 2 ∣ ((H ⊓ M) ⊔ I).relIndex H) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsplit := r95s_relIndex_split (H := H) (A := H ⊓ M) (B := I) inf_le_left hIH hHI
  have hinf : (H ⊓ M) ⊓ I = I ⊓ M := by
    rw [inf_assoc, inf_comm M I, ← inf_assoc, inf_eq_right.mpr hIH]
  have hodd : ¬ 2 ∣ (H ⊓ M).relIndex H := by
    rw [hsplit, hinf]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h | h
    · exact hB h
    · exact hI h
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (H ⊓ M)
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨hSle, hSp, hSodd⟩ := hS
  refine ⟨S, ?_, hSle.trans inf_le_right⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hSle.trans inf_le_left, hSp, ?_⟩
  intro hdvd
  rw [← Subgroup.relIndex_mul_relIndex S (H ⊓ M) H hSle inf_le_left] at hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h | h
  · exact hSodd h
  · exact hodd h

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09

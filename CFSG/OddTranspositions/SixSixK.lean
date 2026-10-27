module

public import CFSG.OddTranspositions.FaithfulBlocks

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

attribute [local instance] blockKernel_normal

theorem normal_odd_sup_odd {A B : Subgroup G} (hA : A.Normal) (hB : B.Normal)
    (hAodd : Odd (Nat.card A)) (hBodd : Odd (Nat.card B)) :
    Odd (Nat.card (A ⊔ B : Subgroup G)) := by
  letI := hA
  letI := hB
  have hindexOdd : Odd (A.relIndex (A ⊔ B)) := by
    rw [Subgroup.relIndex_sup_left]
    exact hBodd.of_dvd_nat (Subgroup.relIndex_dvd_card (H := A) (K := B))
  let within := A.subgroupOf (A ⊔ B)
  have hwithinCard : Nat.card within = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toEquiv
  have hproduct := within.index_mul_card
  have hindex : within.index = A.relIndex (A ⊔ B) := rfl
  rw [hindex, hwithinCard] at hproduct
  rw [← hproduct]
  exact hindexOdd.mul hAodd

theorem oddCore_odd_cfsg : Odd (Nat.card (oddCore G)) := by
  classical
  have hbot : (⊥ : Subgroup G).Normal ∧ Odd (Nat.card (⊥ : Subgroup G)) := by
    exact ⟨inferInstance, by rw [Subgroup.card_bot]; decide⟩
  obtain ⟨maximal, _, hmaximal⟩ := Finite.exists_le_maximal
    (α := Subgroup G) (p := fun H => H.Normal ∧ Odd (Nat.card H)) hbot
  have hallLe : ∀ H : Subgroup G, H.Normal → Odd (Nat.card H) → H ≤ maximal := by
    intro H hHnorm hHodd
    have hsupNormal : (maximal ⊔ H).Normal := by
      letI := hmaximal.prop.1
      letI := hHnorm
      infer_instance
    have hsupOdd := normal_odd_sup_odd hmaximal.prop.1 hHnorm hmaximal.prop.2 hHodd
    have heq := hmaximal.eq_of_le ⟨hsupNormal, hsupOdd⟩ le_sup_left
    exact heq ▸ le_sup_right
  have hequal : oddCore G = maximal := by
    apply le_antisymm
    · exact sSup_le (fun H hH => hallLe H hH.1 hH.2)
    · exact le_sSup ⟨hmaximal.prop.1, hmaximal.prop.2⟩
  rw [hequal]
  exact hmaximal.prop.2

end CFSG.OddTranspositions

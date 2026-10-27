module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Subgroup cardinality inside an index-two layer
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If `J` has index two, `U` crosses `J`, and `A` lies in both `U` and `J`,
then `|A|` divides half of `|U|`. -/
public theorem subgroup_card_dvd_half_of_le_index_two
    {G : Type u} [Group G] [Finite G]
    (J U A : Subgroup G) (hJindex : J.index = 2)
    (hUnotJ : ¬ U ≤ J) (hAU : A ≤ U) (hAJ : A ≤ J) :
    Nat.card A ∣ Nat.card U / 2 := by
  let I : Subgroup G := U ⊓ J
  let IU : Subgroup U := I.subgroupOf U
  rcases Set.not_subset.mp hUnotJ with ⟨a, haU, haJ⟩
  have hIUindex : IU.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨a, haU⟩, ?_, ?_⟩
    · intro haI
      have haI' : a ∈ I := Subgroup.mem_subgroupOf.mp haI
      exact haJ haI'.2
    · intro b
      by_cases hbJ : (b : G) ∈ J
      · right
        apply Subgroup.mem_subgroupOf.mpr
        exact ⟨b.2, hbJ⟩
      · left
        apply Subgroup.mem_subgroupOf.mpr
        refine ⟨U.mul_mem b.2 haU, ?_⟩
        exact (Subgroup.mul_mem_iff_of_index_two hJindex).2
          (iff_of_false hbJ haJ)
  have hIUcardMul : Nat.card IU * 2 = Nat.card U := by
    have h := IU.card_mul_index
    rwa [hIUindex] at h
  have hIUcard : Nat.card IU = Nat.card U / 2 := by omega
  have hIcard : Nat.card I = Nat.card U / 2 := by
    rw [← hIUcard]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show I ≤ U from inf_le_left)).toEquiv).symm
  have hAI : A ≤ I := fun x hx => ⟨hAU hx, hAJ hx⟩
  have hdvd : Nat.card A ∣ Nat.card I := Subgroup.card_dvd_of_le hAI
  rwa [hIcard] at hdvd

end CFSG.GorensteinWalter

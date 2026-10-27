module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinReflectionHall
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A reflection outside the Klein four two-core
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem firstCase_klein_exists_reflection_not_mem_twoCore
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    ∃ s : G, c.IsReflection s ∧ s ∉ twoCoreOf c.Hhat := by
  classical
  by_contra hnot
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS8 : Nat.card (c.S : Subgroup G) = 8 :=
    firstCase_klein_S_card hmin c hfirst hklein
  have h26 := theorem_2_6 hmin c
  have hVleS : twoCoreOf c.Hhat ≤ (c.S : Subgroup G) := by
    rw [← h26.2.1]
    exact inf_le_left
  have hVcard : Nat.card (twoCoreOf c.Hhat) = 4 := by
    simpa using (firstCase_klein_V_klein c hklein).card_four
  have hS0subcard :
      Nat.card (c.S0.subgroupOf (c.S : Subgroup G)) = Nat.card c.S0 := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.S0_le_S).toEquiv
  have hS0index : (c.S0.subgroupOf (c.S : Subgroup G)).index = 2 := by
    have hmul := (c.S0.subgroupOf (c.S : Subgroup G)).index_mul_card
    change (c.S0.subgroupOf (c.S : Subgroup G)).index *
        Nat.card (c.S0.subgroupOf (c.S : Subgroup G)) =
      Nat.card (c.S : Subgroup G) at hmul
    have hS0card : Nat.card c.S0 = 4 := by
      have hSidx := c.S_index_two
      change Nat.card (↥(c.S : Subgroup G)) = 2 * Nat.card (↥c.S0) at hSidx
      rw [hS8] at hSidx
      omega
    rw [hS0subcard, hS0card, hS8] at hmul
    omega
  have hAll : ∀ s : G, c.IsReflection s → s ∈ twoCoreOf c.Hhat := by
    intro s hs
    by_contra hsV
    exact hnot ⟨s, hs, hsV⟩
  obtain ⟨r, hrS, hrnotS0⟩ :
      ∃ r : G, r ∈ (c.S : Subgroup G) ∧ r ∉ c.S0 := by
    have hne : c.S0 ≠ (c.S : Subgroup G) := by
      intro heq
      have hcard : Nat.card (c.S : Subgroup G) =
          2 * Nat.card c.S0 := c.S_index_two
      rw [heq] at hcard
      have hpos : 0 < Nat.card c.S0 := Nat.card_pos
      omega
    exact Set.not_subset.mp (show ¬ (c.S : Subgroup G) ≤ c.S0 from by
      intro hle
      exact hne (le_antisymm c.S0_le_S hle))
  have hrV : r ∈ twoCoreOf c.Hhat := hAll r ⟨hrS, hrnotS0⟩
  have hSleV : (c.S : Subgroup G) ≤ twoCoreOf c.Hhat := by
    intro x hx
    by_cases hx0 : x ∈ c.S0
    · have hRx : r * x ∉ c.S0 := by
        intro hRx0
        have hiff := Subgroup.mul_mem_iff_of_index_two hS0index
          (a := (⟨r, hrS⟩ : c.S))
          (b := (⟨x, c.S0_le_S hx0⟩ : c.S))
        have : (⟨r * x, (c.S : Subgroup G).mul_mem hrS hx⟩ : c.S) ∈
            c.S0.subgroupOf (c.S : Subgroup G) := hRx0
        have hiff' := hiff.mp this
        exact hrnotS0 (hiff'.mpr hx0)
      have hrxV : r * x ∈ twoCoreOf c.Hhat := hAll (r * x)
        ⟨(c.S : Subgroup G).mul_mem hrS hx, hRx⟩
      have hrInv : r⁻¹ = r := by
        exact inv_eq_of_mul_eq_one_right (by
          simpa [pow_two] using
            (centralizerSetup_reflection_isInvolution c ⟨hrS, hrnotS0⟩).2)
      have hr2 : r * r = 1 := by
        simpa [pow_two] using
          (centralizerSetup_reflection_isInvolution c ⟨hrS, hrnotS0⟩).2
      have hrrxV : r⁻¹ * (r * x) ∈ twoCoreOf c.Hhat :=
        (twoCoreOf c.Hhat).mul_mem ((twoCoreOf c.Hhat).inv_mem hrV) hrxV
      rw [show x = r⁻¹ * (r * x) by group]
      exact hrrxV
    · exact hAll x ⟨hx, hx0⟩
  let SsubV := (c.S : Subgroup G).subgroupOf (twoCoreOf c.Hhat)
  have hcard_sub : Nat.card SsubV = Nat.card (c.S : Subgroup G) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleV).toEquiv
  have hcard_le : Nat.card (c.S : Subgroup G) ≤ Nat.card (twoCoreOf c.Hhat) := by
    rw [← hcard_sub]
    exact Subgroup.card_le_card_group SsubV
  omega

end CFSG.GorensteinWalter

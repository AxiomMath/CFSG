module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseOne

import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseOne
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The structural conclusion in Bender's first order-four case

The Case-1 selected-centralizer count gives an order-nine subgroup `Q` whose
normalizer is `Q ⋁ K`.  This packages the full Brauer--Suzuki--Wall
conclusion with `q = 9`, `Q` that selected centralizer, and `D = K`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In Bender's non-containment branch for `|K| = 4`, the selected
order-three centralizer and `K` satisfy the full Brauer--Suzuki--Wall
structural conclusion with parameter `q = 9`. -/
public theorem
    brauerSuzukiWallConclusion_nonempty_of_card_K_eq_four_of_bender_case_one
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (hcase :
      ∃ V X : Subgroup G,
        IsKleinFour V ∧
        Subgroup.centralizer (V : Set G) = V ∧
        Nat.card (Subgroup.normalizer (V : Set G)) = 24 ∧
        X ≤ Subgroup.normalizer (V : Set G) ∧
        Nat.card X = 3 ∧
        ¬ Subgroup.centralizer (X : Set G) ≤
          Subgroup.normalizer (V : Set G)) :
    Nonempty (BrauerSuzukiWallConclusion G) := by
  classical
  obtain ⟨x, hxOrder, htx, hFcard, hAcard, _hHindex, hGcard⟩ :=
    exists_order_nine_selected_centralizer_case_one_data h hk hcase
  have hxne : x ≠ 1 := by
    intro hxone
    rw [hxone, orderOf_one] at hxOrder
    omega
  have hxOutside : x ∉ bswKConjugates h :=
    order_three_not_mem_bswKConjugates h hk hxOrder
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  obtain ⟨hFcomm, hFodd, hFCentInv, _hFHall, _hFTI⟩ :=
    h.inverted_order_three_centralizer_data hk hxOrder htx
  have hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F := by
    intro a haF hane
    exact (hFCentInv a haF hane).1
  have hFinv : ∀ a : G, a ∈ F →
      h.t * a * h.t⁻¹ = a⁻¹ := by
    intro a haF
    by_cases hane : a ≠ 1
    · exact (hFCentInv a haF hane).2
    · have haone : a = 1 := not_ne_iff.mp hane
      subst a
      simp
  have hMdecomp : M = F ⊔ (h.K ⊓ M) := by
    simpa [M, F] using
      selected_centralizer_normalizer_eq_sup_inf_K
        h hxOutside hxne hFodd hFinv
  have hAeqK : h.K ⊓ M = h.K :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by
      have hcard : Nat.card (h.K ⊓ M : Subgroup G) = 4 := by
        simpa [M, F] using hAcard
      rw [hcard, hk])
  have hNormF : Subgroup.normalizer (F : Set G) = F ⊔ h.K := by
    simpa [M, hAeqK] using hMdecomp
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have hFK : Disjoint F h.K := by
    simpa [F] using
      (selected_centralizer_disjoint_H h hxOutside hxne).mono_right hKleH
  have hFcardNine : Nat.card F = 9 := by
    simpa [F] using hFcard
  have hGformula : Nat.card G = 9 * (9 + 1) * (9 - 1) / 2 := by
    calc
      Nat.card G = 360 := hGcard
      _ = 9 * (9 + 1) * (9 - 1) / 2 := by norm_num
  have hKhalf : Nat.card h.K = (9 - 1) / 2 := by
    norm_num [hk]
  exact conclusion_nonempty_of_structural_data
    9 F h.K (by norm_num) hFcardNine hGformula hFCent
      h.K_commutative hFK h.H h.isTISubsetRelative h.s
      h.s_involution h.s_not_mem_K h.H_eq_join h.s_inverts_K
      hNormF hKhalf

end CFSG.GorensteinWalter

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoIntersection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AlternatingFourThreeSubgroupNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The unique normalizing element in the involution coset

Let `T = N_G(H) ∩ N_G(H)^u` for an outside involution `u`.  The subgroup `T`
has order three and is self-normalizing inside `N_G(H) ≃ A₄`.  Consequently,
the only element of the coset `H * u` which normalizes `T` is `u` itself.
-/

open scoped Pointwise
open BenderSuzuki.PFchapter1section1

namespace CFSG.GorensteinWalter

universe u

/-- If `a ∈ H` and `a * u` normalizes the order-three intersection attached
to an outside involution `u`, then `a = 1`.  Equivalently, `u` is the unique
element of `H * u` normalizing that intersection. -/
public theorem
    BrauerSuzukiWallHypotheses.eq_one_of_mem_H_mul_involution_mem_normalizer_inf_rightConjugate_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) {u a : G}
    (huI : IsInvolution u)
    (huN : u ∉ Subgroup.normalizer (h.H : Set G))
    (haH : a ∈ h.H)
    (hau : a * u ∈ Subgroup.normalizer
      ((Subgroup.normalizer (h.H : Set G) ⊓
        rightConjugate (Subgroup.normalizer (h.H : Set G)) u :
          Subgroup G) : Set G)) :
    a = 1 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  let T : Subgroup G := N ⊓ rightConjugate N u
  obtain ⟨hTcard, huNorm, _huInv⟩ :=
    h.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
      hk huI huN
  have hHleN : h.H ≤ N := Subgroup.le_normalizer
  have hTleN : T ≤ N := inf_le_left
  let TN : Subgroup N := T.subgroupOf N
  have hTNcard : Nat.card TN = 3 := by
    calc
      Nat.card TN = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleN).toEquiv
      _ = 3 := hTcard
  have hNiso : Nonempty (N ≃* alternatingGroup (Fin 4)) :=
    h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
  have hTNnorm : Subgroup.normalizer (TN : Set N) = TN :=
    normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
      TN hTNcard hNiso
  have haN : a ∈ N := hHleN haH
  have haNorm : a ∈ Subgroup.normalizer (T : Set G) := by
    have huu : u * u = 1 := by
      simpa [pow_two] using huI.2
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    have hmul := (Subgroup.normalizer (T : Set G)).mul_mem
      (by simpa [T, N] using hau)
      ((Subgroup.normalizer (T : Set G)).inv_mem huNorm)
    simpa [huinv, huu, mul_assoc] using hmul
  let aN : N := ⟨a, haN⟩
  have haNormN : aN ∈ Subgroup.normalizer (TN : Set N) := by
    have haSub : aN ∈ (Subgroup.normalizer (T : Set G)).subgroupOf N :=
      haNorm
    rw [Subgroup.subgroupOf_normalizer_eq hTleN] at haSub
    exact haSub
  have haTN : aN ∈ TN := by
    rw [← hTNnorm]
    exact haNormN
  have haT : a ∈ T := haTN
  let : IsKleinFour h.H := h.isKleinFour_H_of_card_K_eq_two hk
  by_contra hane
  have haSqH := IsKleinFour.mul_self (⟨a, haH⟩ : h.H)
  have haSq : a ^ 2 = 1 := by
    simpa [pow_two] using congrArg Subtype.val haSqH
  have hNne : N ≠ ⊤ := by
    intro htop
    apply huN
    change u ∈ N
    rw [htop]
    trivial
  have hstrong :=
    h.normalizer_H_isStronglyEmbedded_of_card_K_eq_two hk hNne
  exact hstrong.inf_rightConjugate_involutionFree huN (by
    simpa [T, N] using haT) ⟨hane, haSq⟩

end CFSG.GorensteinWalter

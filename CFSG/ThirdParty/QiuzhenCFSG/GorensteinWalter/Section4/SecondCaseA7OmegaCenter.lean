module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaOrder
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaFNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The center of the strict order-27 A7 omega subgroup -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the strict omega branch, the order-27 omega subgroup has center of
order three. -/
public theorem secondCase_a7_omega_center_card_eq_three_of_lt
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d)
    (hAltQ : od.K ⊔ od.F < od.Q.map c.FU.subtype) :
    Nat.card (Subgroup.center (od.Q.map c.FU.subtype)) = 3 := by
  classical
  let A : Subgroup G := od.K ⊔ od.F
  let QG : Subgroup G := od.Q.map c.FU.subtype
  have hAleQ : A ≤ QG := hAltQ.le
  have hFleA : od.F ≤ A := le_sup_right
  have hAcard : Nat.card A = 9 := by
    change Nat.card (od.K ⊔ od.F : Subgroup G) = 9
    rw [od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  let FQ : Subgroup QG := od.F.subgroupOf QG
  let AQ : Subgroup QG := A.subgroupOf QG
  have hAQcard : Nat.card AQ = 9 := by
    calc
      Nat.card AQ = Nat.card A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleQ).toEquiv
      _ = 9 := hAcard
  have hFQleAQ : FQ ≤ AQ := by
    intro f hf
    exact Subgroup.mem_subgroupOf.mpr
      (hFleA (Subgroup.mem_subgroupOf.mp hf))
  have hnormFQ : Subgroup.normalizer (FQ : Set QG) = AQ := by
    simpa [A, QG, FQ, AQ] using
      secondCase_a7_omega_normalizer_F_eq c w d od hAleQ
  have hZleAQ : Subgroup.center QG ≤ AQ := by
    rw [← hnormFQ]
    exact Subgroup.center_le_normalizer (FQ : Set QG)
  have hQcard : Nat.card QG = 3 ^ 3 := by
    have h27 := secondCase_a7_omega_card_eq_twenty_seven_of_lt
      c w d od hAltQ
    change Nat.card (od.Q.map c.FU.subtype) = 3 ^ 3
    rw [h27]
    norm_num
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hkpos, hZcard⟩ :=
    IsPGroup.card_center_eq_prime_pow hQcard (by omega)
  have hZcardLe : Nat.card (Subgroup.center QG) ≤ 9 := by
    rw [← hAQcard]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hZleAQ)
  have hkLe : k ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
    rw [← hZcard]
    norm_num
    exact hZcardLe
  rcases (show k = 1 ∨ k = 2 by omega) with hk | hk
  · simpa [hk] using hZcard
  · have hZAQ : Subgroup.center QG = AQ := by
      apply Subgroup.eq_of_le_of_card_ge hZleAQ
      rw [hZcard, hk, hAQcard]
      norm_num
    have hFQleZ : FQ ≤ Subgroup.center QG := by
      rw [hZAQ]
      exact hFQleAQ
    have hFQnormal : FQ.Normal := by
      refine ⟨?_⟩
      intro f hf q
      have hcomm := Subgroup.mem_center_iff.mp (hFQleZ hf) q
      have hconj : q * f * q⁻¹ = f := by
        rw [hcomm]
        simp
      rw [hconj]
      exact hf
    have hnormTop : Subgroup.normalizer (FQ : Set QG) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hFQnormal
    have hAQtop : AQ = ⊤ := hnormFQ.symm.trans hnormTop
    have hAQneTop : AQ ≠ ⊤ := by
      intro htop
      apply hAltQ.ne
      apply le_antisymm hAleQ
      intro x hx
      have hxAQ : (⟨x, hx⟩ : QG) ∈ AQ := by
        rw [htop]
        simp
      exact Subgroup.mem_subgroupOf.mp hxAQ
    exact (hAQneTop hAQtop).elim

end CFSG.GorensteinWalter

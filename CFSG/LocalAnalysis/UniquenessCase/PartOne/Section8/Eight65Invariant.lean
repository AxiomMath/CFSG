module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SupDecomposition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

variable {G : Type} [Group G]

theorem card_inf_dvd {W Z : Subgroup G} : Nat.card ↥(W ⊓ Z) ∣ Nat.card ↥W := by
  have h := Subgroup.card_subgroup_dvd_card ((W ⊓ Z).subgroupOf W)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ⊓ Z ≤ W)).toEquiv] at h

theorem eq_left_or_right_of_invariant_order_three
    {X Z W : Subgroup G} {t : G}
    (hcomm : ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1)
    (hXcard : Nat.card X = 3) (hZcard : Nat.card Z = 3)
    (hXneZ : X ≠ Z)
    (hX : ∀ x ∈ X, t * x * t⁻¹ = x)
    (hZinv : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹)
    (hW : W ≤ X ⊔ Z) (hWcard : Nat.card W = 3)
    (hWinv : ∀ w ∈ W, t * w * t⁻¹ ∈ W) :
    W = X ∨ W = Z := by
  classical
  rcases eq_or_ne W Z with hWZ | hWZ
  · exact Or.inr hWZ
  left
  haveI hfinX : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hXcard]; norm_num)
  haveI hfinW : Finite ↥W := Nat.finite_of_card_ne_zero (by rw [hWcard]; norm_num)
  haveI hfinZ : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
  have hdisj : W ⊓ Z = ⊥ := by
    have hdvd : Nat.card ↥(W ⊓ Z) ∣ 3 := by
      have := card_inf_dvd (W := W) (Z := Z)
      rwa [hWcard] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · rw [Subgroup.card_eq_one] at h1
      exact h1
    · exfalso
      have hWeq : W ⊓ Z = W :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hWcard])
      have hle : W ≤ Z := hWeq ▸ inf_le_right
      exact hWZ (Subgroup.eq_of_le_of_card_ge hle (by rw [hWcard, hZcard]))
  have hWleX : W ≤ X := by
    intro w hw
    obtain ⟨x, hx, z, hz, rfl⟩ :=
      exists_mul_mem_sup_of_commute (Q := X) (C := Z)
        (fun z hz x hx => (hcomm x hx z hz).symm) (hW hw)
    have ht : t * (x * z) * t⁻¹ = x * z⁻¹ := by
      calc t * (x * z) * t⁻¹ = (t * x * t⁻¹) * (t * z * t⁻¹) := by group
        _ = x * z⁻¹ := by rw [hX x hx, hZinv z hz]
    have hzW : z ∈ W := by
      have h1 : t * (x * z) * t⁻¹ ∈ W := hWinv _ hw
      rw [ht] at h1
      have h2 : (x * z⁻¹) * (x * z)⁻¹ ∈ W := Subgroup.mul_mem W h1 (W.inv_mem hw)
      have h3 : (x * z⁻¹) * (x * z)⁻¹ = z := by
        have hcube : z * z * z = 1 := by
          rw [← pow_three' z]
          exact hZ3 z hz
        have h2 : z * z = z⁻¹ := by
          have h := congrArg (fun w => w * z⁻¹) hcube
          simpa [mul_assoc] using h
        have hzz : z⁻¹ * z⁻¹ = z := by
          rw [← h2]
          calc (z * z) * (z * z) = (z * z * z) * z := by group
            _ = 1 * z := by rw [hcube]
            _ = z := by rw [one_mul]
        rw [mul_inv_rev]
        calc x * z⁻¹ * (z⁻¹ * x⁻¹) = x * (z⁻¹ * z⁻¹) * x⁻¹ := by group
          _ = x * z * x⁻¹ := by rw [hzz]
          _ = z * x * x⁻¹ := by rw [hcomm x hx z hz]
          _ = z := by group
      rwa [h3] at h2
    have hzZ : z ∈ Z := hz
    have hzbot : z ∈ W ⊓ Z := Subgroup.mem_inf.mpr ⟨hzW, hzZ⟩
    rw [hdisj] at hzbot
    have hz1 : z = 1 := Subgroup.mem_bot.mp hzbot
    rwa [hz1, mul_one]
  exact Subgroup.eq_of_le_of_card_ge hWleX (by rw [hWcard, hXcard])

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

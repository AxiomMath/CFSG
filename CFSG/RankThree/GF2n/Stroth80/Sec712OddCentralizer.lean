module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem commOfOddCentralizer_holds :
    ∀ (H : Type) [Group H] (R N D : Subgroup H), R.Normal → D.Normal → IsPGroup 2 N →
      (∀ x ∈ D, ∀ c ∈ N, x * c = c * x) → D ⊓ R ≤ N →
      ∀ x ∈ D, Odd (orderOf x) → ∀ r ∈ R, r * x = x * r := by
  intro H _ R N D hR hD hN hcent hDR x hxD hodd r hrR
  obtain ⟨c, hc⟩ : ∃ c : H, c = r * x * r⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hcR : c ∈ R := by
    have h1 : x * r⁻¹ * x⁻¹ ∈ R := hR.conj_mem r⁻¹ (R.inv_mem hrR) x
    have h2 : c = r * (x * r⁻¹ * x⁻¹) := by simp only [hc, mul_assoc]
    rw [h2]
    exact R.mul_mem hrR h1
  have hcD : c ∈ D := by
    have h1 : r * x * r⁻¹ ∈ D := hD.conj_mem x hxD r
    rw [hc]
    exact D.mul_mem h1 (D.inv_mem hxD)
  have hcDR : c ∈ D ⊓ R := Subgroup.mem_inf.mpr ⟨hcD, hcR⟩
  have hcN : c ∈ N := hDR hcDR
  have hcomm : Commute c x := (hcent x hxD c hcN).symm
  have hrxr : r * x * r⁻¹ = c * x := by
    rw [hc]
    simp
  have hpow1 : (r * x * r⁻¹) ^ orderOf x = 1 := by
    rw [conj_pow, pow_orderOf_eq_one x]
    simp
  have hcx : (c * x) ^ orderOf x = 1 := by
    rw [← hrxr]
    exact hpow1
  have hcp : c ^ orderOf x = 1 := by
    have h := hcomm.mul_pow (orderOf x)
    rw [pow_orderOf_eq_one x, mul_one] at h
    rw [← h]
    exact hcx
  obtain ⟨k, hk⟩ := hN ⟨c, hcN⟩
  have hk' : c ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hcop : Nat.gcd (orderOf x) (2 ^ k) = 1 :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)).symm
  have hc1 : c = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hcp, hk'⟩
    rw [hcop, pow_one] at h
    exact h
  have hfin : r * x * r⁻¹ * x⁻¹ = 1 := by
    rw [← hc]
    exact hc1
  have h2 : r * x * r⁻¹ = x := mul_inv_eq_one.mp hfin
  calc r * x = r * x * r⁻¹ * r := by simp
    _ = x * r := by rw [h2]

end CFSG.RankThree.GF2n.Stroth80

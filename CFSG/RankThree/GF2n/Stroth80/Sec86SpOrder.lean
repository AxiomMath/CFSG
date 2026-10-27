module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem exists_odd_card_statedSp {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (m : ℕ) :
    ∃ o : ℕ, Odd o ∧ Nat.card ↥(CFSG.Open.StatedSp m K) = (2 ^ f) ^ (m ^ 2) * o := by
  have hf0 : f ≠ 0 := by omega
  have hodd : ∀ j ∈ Finset.Icc 1 m, Odd ((2 ^ f) ^ (2 * j) - 1 : ℕ) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj0 : 2 * j ≠ 0 := by omega
    have hdvd : (2 : ℕ) ∣ (2 ^ f) ^ (2 * j) :=
      dvd_trans (dvd_pow_self 2 hf0) (dvd_pow_self (2 ^ f) hj0)
    have hpos : (0 : ℕ) < (2 ^ f) ^ (2 * j) := by positivity
    obtain ⟨t, ht⟩ := hdvd
    rw [Nat.odd_iff, ht]
    rw [ht] at hpos
    omega
  refine ⟨∏ j ∈ Finset.Icc 1 m, ((2 ^ f) ^ (2 * j) - 1),
    Finset.prod_induction (fun j : ℕ => ((2 ^ f) ^ (2 * j) - 1 : ℕ)) Odd
      (fun a b ha hb => Odd.mul ha hb) odd_one hodd, ?_⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) (r := m), hK]

theorem two_adic_ineq {a b g o₁ o₂ X : ℕ} (ho₁ : Odd o₁) (ho₂ : Odd o₂)
    (h : 2 ^ a * o₁ = X * 2 ^ g) (hX : X ∣ 2 ^ b * o₂) : a ≤ b + g := by
  by_contra hlt
  obtain ⟨d, rfl⟩ : ∃ d, a = b + g + d := ⟨a - (b + g), by omega⟩
  have hd : d ≠ 0 := by omega
  have h1 : 2 ^ (b + g + d) * o₁ ∣ 2 ^ (b + g) * o₂ := by
    rw [h]
    have h2 := Nat.mul_dvd_mul_right hX (2 ^ g)
    have h3 : 2 ^ b * o₂ * 2 ^ g = 2 ^ (b + g) * o₂ := by ring
    rw [h3] at h2
    exact h2
  have h5 : 2 ^ (b + g) * 2 ^ d ∣ 2 ^ (b + g + d) * o₁ := by
    rw [← pow_add]
    exact dvd_mul_right _ _
  have h4 : 2 ^ (b + g) * 2 ^ d ∣ 2 ^ (b + g) * o₂ := dvd_trans h5 h1
  have hpos : (0 : ℕ) < 2 ^ (b + g) := by positivity
  have h6 : 2 ^ d ∣ o₂ := (Nat.mul_dvd_mul_iff_left hpos).mp h4
  have h7 : (2 : ℕ) ∣ o₂ := dvd_trans (dvd_pow_self 2 hd) h6
  obtain ⟨c, hc⟩ := h7
  obtain ⟨e, he⟩ := ho₂
  omega

end CFSG.RankThree.GF2n.Stroth80

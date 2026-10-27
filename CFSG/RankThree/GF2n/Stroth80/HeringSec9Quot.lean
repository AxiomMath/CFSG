module

public import CFSG.RankThree.GF2n.Stroth80.Sec33Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

namespace HS9

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_right_of_le_normalizer {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer (L := B) (E := A) hA
  have hB : B ≤ A ⊔ B := le_sup_right
  have e1 : B.relIndex (A ⊔ B) * Nat.card ↥B = Nat.card ↥(A ⊔ B) := by
    have := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
    rwa [inf_eq_left.mpr hB] at this
  have e2 : B.relIndex A * Nat.card ↥(B ⊓ A) = Nat.card ↥A :=
    Subgroup.relIndex_mul_card B A
  rw [sup_comm] at h1
  have hpos : 0 < Nat.card ↥(B ⊓ A) := Nat.card_pos
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hBpos ?_
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc B.relIndex (A ⊔ B) * Nat.card ↥B * Nat.card ↥(B ⊓ A)
      = Nat.card ↥(A ⊔ B) * Nat.card ↥(B ⊓ A) := by rw [e1]
    _ = Nat.card ↥B * Nat.card ↥A := h1
    _ = B.relIndex A * Nat.card ↥(B ⊓ A) * Nat.card ↥B := by rw [e2, mul_comm]
    _ = B.relIndex A * Nat.card ↥B * Nat.card ↥(B ⊓ A) := by ring

theorem relIndex_dvd_of_normalizes {A B C : Subgroup G} (hAC : A ≤ C) (hBC : B ≤ C)
    (hA : A ≤ Subgroup.normalizer (B : Set G)) : B.relIndex A ∣ B.relIndex C := by
  rw [← relIndex_sup_right_of_le_normalizer hA]
  exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex B (A ⊔ B) C le_sup_right (sup_le hAC hBC))

theorem relIndex_two_pow_of_isPGroup {A : Subgroup G} (B : Subgroup G) (hA : IsPGroup 2 ↥A) :
    ∃ k : ℕ, B.relIndex A = 2 ^ k := by
  obtain ⟨m, hm⟩ := hA.exists_card_eq
  have hdvd : B.relIndex A ∣ 2 ^ m := hm ▸ Subgroup.relIndex_dvd_card B A
  exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd |>.imp fun k hk => hk.2

theorem normalizer_of_commutator_le {X Y Q : Subgroup G} (hQX : Q ≤ X)
    (hcomm : ∀ a ∈ X, ∀ y ∈ Y, ⁅a, y⁆ ∈ Q) : Y ≤ Subgroup.normalizer (X : Set G) := by
  have key : ∀ y ∈ Y, ∀ h ∈ X, y * h * y⁻¹ ∈ X := by
    intro y hy h hh
    have h1 : ⁅h, y⁆⁻¹ ∈ X := X.inv_mem (hQX (hcomm h hh y hy))
    have e : y * h * y⁻¹ = ⁅h, y⁆⁻¹ * h := by simp only [commutatorElement_def]; group
    rw [e]
    exact X.mul_mem h1 hh
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key y hy h hh, fun hh => ?_⟩
  have := key y⁻¹ (Y.inv_mem hy) _ hh
  simpa [mul_assoc] using this

theorem le_of_two_pow_dvd_mul_sq_sub_one {q k : ℕ} (hq : 2 ∣ q) (hq0 : 0 < q)
    (h : 2 ^ k ∣ q * (q ^ 2 - 1)) : 2 ^ k ≤ q := by
  have hodd : Odd (q ^ 2 - 1) := by
    obtain ⟨c, rfl⟩ := hq
    have hc1 : 1 ≤ c := by omega
    have e : (2 * c) ^ 2 = 4 * (c * c) := by ring
    rw [e]
    have ht : 1 ≤ c * c := Nat.mul_pos hc1 hc1
    generalize c * c = u at ht
    exact ⟨2 * u - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) (q ^ 2 - 1) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  exact Nat.le_of_dvd hq0 (hcop.dvd_of_dvd_mul_right h)

end HS9

end CFSG.RankThree.GF2n.Stroth80

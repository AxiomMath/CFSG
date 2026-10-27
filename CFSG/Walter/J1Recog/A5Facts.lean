module

public import CFSG.Walter.J1.A5Sub

public section

namespace CFSG.Walter.J1Recog

namespace A5F

private instance instDecEqPermFin5 : DecidableEq (Equiv.Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

private instance instDecMemA5 :
    DecidablePred (fun σ : Equiv.Perm (Fin 5) => σ ∈ alternatingGroup (Fin 5)) :=
  Equiv.Perm.sign.decidableMemKer

abbrev A := alternatingGroup (Fin 5)

set_option maxHeartbeats 0 in
theorem ct_fact : ∀ m : A, (m ^ 3 = 1 ∧ m ≠ 1) → ∀ u : A,
    (u ^ 2 = 1 ∧ u ≠ 1 ∧ u * m * u⁻¹ = m⁻¹) → ∀ v : A,
    (v ^ 2 = 1 ∧ v ≠ 1 ∧ v ≠ m⁻¹ * v * m ∧
      v * (m⁻¹ * v * m) = m⁻¹ * (m⁻¹ * v * m) * m) →
    ∃ k : Fin 3, (u * m ^ (k : ℕ) * v) ^ 5 = 1 ∧ u * m ^ (k : ℕ) * v ≠ 1 ∧
      (u * m ^ (k : ℕ) * (m⁻¹ * v * m)) ^ 3 = 1 ∧ u * m ^ (k : ℕ) * (m⁻¹ * v * m) ≠ 1 ∧
      (u * m ^ (k : ℕ) * (m⁻¹ * (m⁻¹ * v * m) * m)) ^ 5 = 1 ∧
      u * m ^ (k : ℕ) * (m⁻¹ * (m⁻¹ * v * m) * m) ≠ 1 ∧
      (m * (u * m ^ (k : ℕ)) * (m⁻¹ * (m⁻¹ * v * m) * m)) ^ 3 = 1 ∧
      m * (u * m ^ (k : ℕ)) * (m⁻¹ * (m⁻¹ * v * m) * m) ≠ 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem split_fact : ∀ x : A, (x ^ 2 = 1 ∧ x ≠ 1) → ∀ a : A,
    (a ^ 2 = 1 ∧ a ≠ 1 ∧ (a * x) ^ 3 = 1 ∧ a * x ≠ 1) → ∀ w : A,
    (w ^ 2 = 1 ∧ w ≠ 1 ∧ w * x = x * w ∧ w ≠ x) → ∀ q : A,
    (q ^ 3 = 1 ∧ q ≠ 1 ∧ x * q * x⁻¹ = q⁻¹) →
    (a * x = q ∨ a * x = q ^ 2 ∨ w * (a * x) * w⁻¹ = q ∨ w * (a * x) * w⁻¹ = q ^ 2) := by
  decide +kernel

end A5F

namespace A5Sub

open CFSG.Walter.J1.A5Sub

variable {G : Type*} [Group G] {F : Subgroup G} (e : F ≃* alternatingGroup (Fin 5))
include e

theorem ct_fact {m u v : G} (hm : m ∈ F) (hu : u ∈ F) (hv : v ∈ F) (hm3 : m ^ 3 = 1)
    (hm1 : m ≠ 1) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (hum : u * m * u⁻¹ = m⁻¹) (hv2 : v ^ 2 = 1)
    (hv1 : v ≠ 1) (hvv : v ≠ m⁻¹ * v * m)
    (hvvv : v * (m⁻¹ * v * m) = m⁻¹ * (m⁻¹ * v * m) * m) :
    ∃ k : Fin 3, (u * m ^ (k : ℕ) * v) ^ 5 = 1 ∧ u * m ^ (k : ℕ) * v ≠ 1 ∧
      (u * m ^ (k : ℕ) * (m⁻¹ * v * m)) ^ 3 = 1 ∧ u * m ^ (k : ℕ) * (m⁻¹ * v * m) ≠ 1 ∧
      (u * m ^ (k : ℕ) * (m⁻¹ * (m⁻¹ * v * m) * m)) ^ 5 = 1 ∧
      u * m ^ (k : ℕ) * (m⁻¹ * (m⁻¹ * v * m) * m) ≠ 1 ∧
      (m * (u * m ^ (k : ℕ)) * (m⁻¹ * (m⁻¹ * v * m) * m)) ^ 3 = 1 ∧
      m * (u * m ^ (k : ℕ)) * (m⁻¹ * (m⁻¹ * v * m) * m) ≠ 1 := by
  obtain ⟨a, rfl⟩ := exists_ι e hm
  obtain ⟨b, rfl⟩ := exists_ι e hu
  obtain ⟨c, rfl⟩ := exists_ι e hv
  simp only [← map_pow, ← map_mul, ← map_inv, ι_eq_one_iff, ne_eq, ι_eq_iff] at *
  exact A5F.ct_fact a ⟨hm3, hm1⟩ b ⟨hu2, hu1, hum⟩ c ⟨hv2, hv1, hvv, hvvv⟩

theorem split_fact {x a w q : G} (hx : x ∈ F) (ha : a ∈ F) (hw : w ∈ F) (hq : q ∈ F)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (hax3 : (a * x) ^ 3 = 1)
    (hax1 : a * x ≠ 1) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) (hwx : w * x = x * w) (hwx' : w ≠ x)
    (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1) (hxq : x * q * x⁻¹ = q⁻¹) :
    a * x = q ∨ a * x = q ^ 2 ∨ w * (a * x) * w⁻¹ = q ∨ w * (a * x) * w⁻¹ = q ^ 2 := by
  obtain ⟨x', rfl⟩ := exists_ι e hx
  obtain ⟨a', rfl⟩ := exists_ι e ha
  obtain ⟨w', rfl⟩ := exists_ι e hw
  obtain ⟨q', rfl⟩ := exists_ι e hq
  simp only [← map_pow, ← map_mul, ← map_inv, ι_eq_one_iff, ne_eq, ι_eq_iff] at *
  exact A5F.split_fact x' ⟨hx2, hx1⟩ a' ⟨ha2, ha1, hax3, hax1⟩ w' ⟨hw2, hw1, hwx, hwx'⟩ q'
    ⟨hq3, hq1, hxq⟩

theorem conj_three {x y : G} (hx : x ∈ F) (hy : y ∈ F) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) : ∃ f ∈ F, f * x * f⁻¹ = y := by
  obtain ⟨x', rfl⟩ := exists_ι e hx
  obtain ⟨y', rfl⟩ := exists_ι e hy
  simp only [← map_pow, ι_eq_one_iff, ne_eq] at hx3 hx1 hy3 hy1
  obtain ⟨g, hg⟩ := CFSG.Walter.J1.A5.conj_three x' y' ⟨hx3, hx1, hy3, hy1⟩
  exact ⟨ι e g, ι_mem e g, by rw [← map_inv, ← map_mul, ← map_mul, hg]⟩

end A5Sub

end CFSG.Walter.J1Recog

module

public import CFSG.Quasithin.Vol2.Ch11SecJSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open scoped MatrixGroups

theorem ne_inv_pow_three {F : Type*} [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) : c ≠ (c ^ 3)⁻¹ := by
  intro h
  have h3 : c * c ^ 3 = 1 := by
    calc c * c ^ 3 = (c ^ 3)⁻¹ * c ^ 3 := by rw [← h]
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero 3 hc0)
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h5 : (c - 1) ^ 4 = 0 := by
    linear_combination h3 + (-2 * c ^ 3 + 3 * c ^ 2 - 2 * c + 1) * h2
  exact hc1 (sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).1 h5))

theorem exists_ne_zero_ne_one {n : ℕ} (hn : 1 < n) : ∃ c : GaloisField 2 n, c ≠ 0 ∧ c ≠ 1 := by
  rcases card_two_or_exists_sq_ne_one (F := GaloisField 2 n) with h2 | ⟨a, ha0, ha1⟩
  · exfalso
    rw [GaloisField.card 2 n (by omega)] at h2
    have h3 : 2 ^ n = 2 ^ 1 := by rw [h2, pow_one]
    have := Nat.pow_right_injective (le_refl 2) h3
    omega
  · exact ⟨a, ha0, fun h => ha1 (by rw [h, one_pow])⟩

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

namespace Core

variable (C : Core G T L I n V₁)

theorem exists_x : ∃ (x : ↥L) (c : GaloisField 2 n) (hc : c ≠ 0), c ≠ 1 ∧
    C.St.D.θ x = dg c hc := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one C.h.one_lt
  obtain ⟨x, hx⟩ := C.St.D.surj (dg c hc0)
  exact ⟨x, c, hc0, hc1, hx⟩

variable {C}

theorem x_mem_G₁ {x : ↥L} {c : GaloisField 2 n} {hc : c ≠ 0} (hx : C.St.D.θ x = dg c hc) :
    (x : G) ∈ Subgroup.normalizer (V₁ : Set G) :=
  C.St.mem_normalizer_V₁_of_stab x (hx ▸ dg_mem_Pt c hc)

theorem x_mem_normalizer_lOf {x : ↥L} {c : GaloisField 2 n} {hc : c ≠ 0}
    (hx : C.St.D.θ x = dg c hc) : (x : G) ∈ Subgroup.normalizer (LOf L V₁ : Set G) :=
  normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer ⟨x.2, x_mem_G₁ hx⟩)

theorem x_comm_mem_U {x : ↥L} {c : GaloisField 2 n} {hc : c ≠ 0} (hx : C.St.D.θ x = dg c hc)
    {k : G} (hk : k ∈ LOf L V₁) :
    (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈
      conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) := by
  have h := C.mem_U_of_theta_mem_Qv (x * ⟨k, lOf_le_L hk⟩ * x⁻¹ * ⟨k, lOf_le_L hk⟩⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx]
    exact dg_comm_mem_Qv c hc (C.theta_mem_Pt ⟨k, hk⟩))
  simpa using h

end Core

end CFSG.Quasithin.Vol2.Ch11.SecJ

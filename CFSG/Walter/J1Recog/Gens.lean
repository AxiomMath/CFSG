module

public import CFSG.Walter.J1Recog.Local
public import CFSG.Walter.J1Recog.A5Facts

public section

namespace CFSG.Walter.J1Recog

open CFSG.Walter.J1

namespace Setup

variable {G : Type} [Group G] [Finite G] (X : Setup G)

theorem t_not_inv_n : X.t * X.n * X.t⁻¹ ≠ X.n⁻¹ := by
  intro htn
  have he1 : X.e 1 * X.t = X.n⁻¹ ^ 2 := by
    have h1 : X.t * X.n = X.n⁻¹ * X.t := by rw [← htn]; group
    simp only [e, ee, pow_one]
    calc X.n⁻¹ * X.t * X.n * X.t = X.n⁻¹ * (X.t * X.n) * X.t := by group
      _ = X.n⁻¹ * (X.n⁻¹ * X.t) * X.t := by rw [h1]
      _ = X.n⁻¹ ^ 2 := by
        rw [mul_assoc, mul_assoc, X.t_mul_t, mul_one]; exact (pow_two _).symm
  have hmem : X.n⁻¹ ^ 2 ∈ (X.S : Subgroup G) := by
    rw [← he1]; exact Subgroup.mul_mem _ (X.e_mem 1) X.t_mem
  have h4 : X.n ^ 4 = 1 := by
    have := X.mem_mul_self hmem
    rw [← pow_add, inv_pow] at this
    exact inv_eq_one.mp this
  apply X.n_ne_one
  calc X.n = X.n ^ 8 * (X.n ^ 7)⁻¹ := by group
    _ = 1 := by rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, h4, one_pow, X.n_pow_seven, inv_one,
      mul_one]

@[expose] def Pattern (x : G) : Prop :=
  ((x * X.e 5) ^ 5 = 1 ∧ x * X.e 5 ≠ 1) ∧ ((x * X.e 3) ^ 3 = 1 ∧ x * X.e 3 ≠ 1) ∧
    ((x * X.e 6) ^ 5 = 1 ∧ x * X.e 6 ≠ 1) ∧ ((X.m * x * X.e 6) ^ 3 = 1 ∧ X.m * x * X.e 6 ≠ 1)

theorem m_e_inv (i : ℕ) : X.m * X.e i * X.m⁻¹ = X.e (4 * i) := by
  have h := X.m_e (4 * i)
  rw [← X.e_mod (2 * (4 * i)), show 2 * (4 * i) % 7 = i % 7 by omega, X.e_mod] at h
  rw [← h]
  group

theorem exists_pattern {x : G} (hxF : x ∈ X.F) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxm : x * X.m * x⁻¹ = X.m⁻¹) : ∃ k : ℕ, X.Pattern (x * X.m ^ k) := by
  have he5 : X.e 5 ∈ X.F := X.e5_mem_F
  have hme5 : X.m⁻¹ * X.e 5 * X.m = X.e 3 := by
    rw [X.m_e, ← X.e_mod, show 2 * 5 % 7 = 3 from rfl]
  have hme3 : X.m⁻¹ * X.e 3 * X.m = X.e 6 := X.m_e 3
  obtain ⟨k, h1, h2, h3, h4, h5, h6, h7, h8⟩ := A5Sub.ct_fact X.h.iso X.m_mem_F hxF he5
    X.m_pow_three X.m_ne_one (by rw [pow_two]; exact hx2) hx1 hxm
    (by rw [pow_two]; exact X.e_mul_self 5) (X.e_ne_one 5)
    (by rw [hme5]; exact (X.e_ne (by norm_num) (by norm_num)).symm)
    (by rw [hme5, hme3, X.e_comm]; have := X.rel_shift 3; simpa using this)
  rw [hme5] at h3 h4 h5 h6 h7 h8
  rw [hme3] at h5 h6 h7 h8
  exact ⟨k, ⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩⟩

theorem exists_gens : ∃ s u x : G, orderOf s = 2 ∧ s * X.n * s⁻¹ = X.n⁻¹ ∧ s * X.m = X.m * s ∧
    orderOf u = 2 ∧ u * X.t = X.t * u ∧ u * s = s * u ∧ u * X.m * u⁻¹ = X.m⁻¹ ∧
    x ∈ X.F ∧ (x = u ∨ x = X.t * u) ∧ X.Pattern x := by
  obtain ⟨s, hs, hsn, hsm⟩ := X.exists_s
  have hst : s ≠ X.t := by
    rintro rfl
    exact X.t_not_inv_n hsn
  obtain ⟨u₀, hu₀, hu₀t, hu₀s, hu₀m⟩ := X.exists_u hs hsm hst
  have hu₀2 : u₀ * u₀ = 1 := (orderOf_eq_two_iff.mp hu₀).1
  have hu₀inv : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right hu₀2
  obtain ⟨x₀, hx₀F, hx₀u, hx₀2, hx₀1, hx₀m⟩ : ∃ x₀ ∈ X.F, (x₀ = u₀ ∨ x₀ = X.t * u₀) ∧
      x₀ * x₀ = 1 ∧ x₀ ≠ 1 ∧ x₀ * X.m * x₀⁻¹ = X.m⁻¹ := by
    have hu₀C : u₀ ∈ Subgroup.centralizer ({X.t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hu₀t
    rcases X.h.mem_centralizer_t.mp hu₀C with hF | hF
    · exact ⟨u₀, hF, Or.inl rfl, hu₀2, (orderOf_eq_two_iff.mp hu₀).2, hu₀m⟩
    · refine ⟨X.t * u₀, hF, Or.inr rfl, ?_, ?_, ?_⟩
      · calc X.t * u₀ * (X.t * u₀) = X.t * (u₀ * X.t) * u₀ := by group
          _ = 1 := by rw [hu₀t, ← mul_assoc, X.t_mul_t, one_mul, hu₀2]
      · intro h1
        have h2 : u₀ = X.t := by
          have : u₀ = X.t * (X.t * u₀) := by rw [← mul_assoc, X.t_mul_t, one_mul]
          rw [this, h1, mul_one]
        rw [h2, ← X.m_t, mul_inv_cancel_right] at hu₀m
        apply X.m_ne_one
        have hm2 : X.m * X.m = 1 := by
          calc X.m * X.m = X.m * X.m⁻¹ := by rw [← hu₀m]
            _ = 1 := mul_inv_cancel _
        calc X.m = X.m ^ 3 * (X.m * X.m)⁻¹ := by group
          _ = 1 := by rw [X.m_pow_three, hm2, inv_one, one_mul]
      · have htmt : X.t * X.m * X.t⁻¹ = X.m := by rw [← X.m_t, mul_inv_cancel_right]
        calc X.t * u₀ * X.m * (X.t * u₀)⁻¹ = X.t * (u₀ * X.m * u₀⁻¹) * X.t⁻¹ := by group
          _ = X.m⁻¹ := by rw [hu₀m, ← inv_inj, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv,
            ← mul_assoc, htmt]
  obtain ⟨k, hk⟩ := X.exists_pattern hx₀F hx₀2 hx₀1 hx₀m
  have hmk : ∀ j : ℕ, u₀ * X.m ^ j * u₀⁻¹ = (X.m⁻¹) ^ j := by
    intro j; rw [← conj_pow, hu₀m]
  refine ⟨s, u₀ * X.m ^ k, x₀ * X.m ^ k, hs, hsn, hsm, ?_, ?_, ?_, ?_, ?_, ?_, hk⟩
  · refine orderOf_eq_two_iff.mpr ⟨?_, ?_⟩
    · calc u₀ * X.m ^ k * (u₀ * X.m ^ k) = (u₀ * X.m ^ k * u₀⁻¹) * X.m ^ k := by
            rw [hu₀inv]; group
        _ = 1 := by rw [hmk, inv_pow, inv_mul_cancel]
    · intro h1
      have : u₀ = (X.m ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : orderOf u₀ ∣ 3 := by
        rw [this, orderOf_inv]
        exact orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, X.m_pow_three,
          one_pow])
      rw [hu₀] at h3
      omega
  · have hmt : X.m ^ k * X.t = X.t * X.m ^ k := (Commute.pow_left (show Commute X.m X.t from
      X.m_t) k).eq
    rw [mul_assoc, hmt, ← mul_assoc, hu₀t, mul_assoc]
  · have hms : X.m ^ k * s = s * X.m ^ k := (Commute.pow_left (show Commute X.m s from
      hsm.symm) k).eq
    rw [mul_assoc, hms, ← mul_assoc, hu₀s, mul_assoc]
  · calc u₀ * X.m ^ k * X.m * (u₀ * X.m ^ k)⁻¹ = u₀ * X.m * u₀⁻¹ := by group
      _ = X.m⁻¹ := hu₀m
  · exact X.F.mul_mem hx₀F (X.F.pow_mem X.m_mem_F k)
  · rcases hx₀u with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (mul_assoc _ _ _)

end Setup

end CFSG.Walter.J1Recog

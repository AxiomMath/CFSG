module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5B

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra Module

local notation "F" => OmegaField

variable {V : Type*} [AddCommGroup V] [Module F V]

private theorem s16h_e3_z3f5_e_sub_apply {f : Module.End F V} (hf5 : f ^ 5 = 1) (v : V) :
    s16h_e3_z3f5_e f ((1 - s16h_e3_z3f5_e f) v) = 0 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, s16h_e3_z3f5_e_e hf5, sub_self]

private theorem s16h_e3_z3f5_sub_e_apply {f : Module.End F V} (hf5 : f ^ 5 = 1) (v : V) :
    (1 - s16h_e3_z3f5_e f) (s16h_e3_z3f5_e f v) = 0 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, s16h_e3_z3f5_e_e hf5, sub_self]

private theorem s16h_e3_z3f5_sub_sub_apply {f : Module.End F V} (hf5 : f ^ 5 = 1) (v : V) :
    (1 - s16h_e3_z3f5_e f) ((1 - s16h_e3_z3f5_e f) v) = (1 - s16h_e3_z3f5_e f) v := by
  rw [LinearMap.sub_apply, Module.End.one_apply, s16h_e3_z3f5_e_sub_apply hf5, sub_zero]

theorem s16h_e3_z3f5_diag_mul {f : Module.End F V} (hf5 : f ^ 5 = 1) (a b c d : F) :
    (a • (1 - s16h_e3_z3f5_e f) + b • s16h_e3_z3f5_e f) *
        (c • (1 - s16h_e3_z3f5_e f) + d • s16h_e3_z3f5_e f) =
      (a * c) • (1 - s16h_e3_z3f5_e f) + (b * d) • s16h_e3_z3f5_e f := by
  ext v
  rw [Module.End.mul_apply]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
  rw [s16h_e3_z3f5_e_sub_apply hf5, s16h_e3_z3f5_sub_e_apply hf5,
    s16h_e3_z3f5_sub_sub_apply hf5, s16h_e3_z3f5_e_e hf5]
  simp only [smul_zero, add_zero, zero_add]
  module

theorem s16h_e3_z3f5_exists_e_eq_zero {f : Module.End F V} (hf5 : f ^ 5 = 1)
    (hf1 : f ≠ 1) : ∃ u : V, u ≠ 0 ∧ s16h_e3_z3f5_e f u = 0 := by
  have : ∃ v, s16h_e3_z3f5_e f v ≠ v := by
    by_contra h
    push Not at h
    apply hf1
    ext v
    rw [Module.End.one_apply, ← h v, s16h_e3_z3f5_f_e hf5]
  obtain ⟨v, hv⟩ := this
  exact ⟨v - s16h_e3_z3f5_e f v, sub_ne_zero.mpr hv.symm,
    by rw [map_sub, s16h_e3_z3f5_e_e hf5, sub_self]⟩

noncomputable def s16h_e3_z3f5_diagUnit {f : (Module.End F V)ˣ}
    (hf5 : (f : Module.End F V) ^ 5 = 1) (α μ : Fˣ) : (Module.End F V)ˣ where
  val := (α : F) • (1 - s16h_e3_z3f5_e (f : Module.End F V)) +
    (μ : F) • s16h_e3_z3f5_e (f : Module.End F V)
  inv := (↑α⁻¹ : F) • (1 - s16h_e3_z3f5_e (f : Module.End F V)) +
    (↑μ⁻¹ : F) • s16h_e3_z3f5_e (f : Module.End F V)
  val_inv := by
    rw [s16h_e3_z3f5_diag_mul hf5]
    simp
  inv_val := by
    rw [s16h_e3_z3f5_diag_mul hf5]
    simp

noncomputable def s16h_e3_z3f5_diagHom {f : (Module.End F V)ˣ}
    (hf5 : (f : Module.End F V) ^ 5 = 1) :
    (Fˣ × Fˣ) →* (Module.End F V)ˣ where
  toFun p := s16h_e3_z3f5_diagUnit hf5 p.1 p.2
  map_one' := by
    apply Units.ext
    ext v
    simp [s16h_e3_z3f5_diagUnit]
  map_mul' p q := by
    apply Units.ext
    simp only [s16h_e3_z3f5_diagUnit, Units.val_mul]
    rw [s16h_e3_z3f5_diag_mul hf5]
    rfl

@[simp] theorem s16h_e3_z3f5_diagUnit_val {f : (Module.End F V)ˣ}
    (hf5 : (f : Module.End F V) ^ 5 = 1) (α μ : Fˣ) :
    ((s16h_e3_z3f5_diagUnit hf5 α μ : (Module.End F V)ˣ) : Module.End F V) =
      (α : F) • (1 - s16h_e3_z3f5_e (f : Module.End F V)) +
      (μ : F) • s16h_e3_z3f5_e (f : Module.End F V) := rfl

@[simp] theorem s16h_e3_z3f5_diagHom_apply {f : (Module.End F V)ˣ}
    (hf5 : (f : Module.End F V) ^ 5 = 1) (p : Fˣ × Fˣ) :
    s16h_e3_z3f5_diagHom hf5 p = s16h_e3_z3f5_diagUnit hf5 p.1 p.2 := rfl

theorem s16h_e3_z3f5_orderOf_eq_five {f : (Module.End F V)ˣ}
    (hf5 : (f : Module.End F V) ^ 5 = 1) (hf1 : (f : Module.End F V) ≠ 1) :
    orderOf f = 5 := by
  have hdvd : orderOf f ∣ 5 := orderOf_dvd_of_pow_eq_one (Units.ext hf5)
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
  · exact absurd (congrArg Units.val (orderOf_eq_one_iff.mp h)) hf1
  · exact h

variable [FiniteDimensional F V]

theorem s16h_e3_z3f5_diagHom_injective {f : (Module.End F V)ˣ}
    (hV : finrank F V = 3) (hf5 : (f : Module.End F V) ^ 5 = 1)
    (hf1 : (f : Module.End F V) ≠ 1) :
    Function.Injective (s16h_e3_z3f5_diagHom (V := V) hf5) := by
  intro p q hpq
  have hval : (p.1 : F) • (1 - s16h_e3_z3f5_e (f : Module.End F V)) +
      (p.2 : F) • s16h_e3_z3f5_e (f : Module.End F V) =
      (q.1 : F) • (1 - s16h_e3_z3f5_e (f : Module.End F V)) +
      (q.2 : F) • s16h_e3_z3f5_e (f : Module.End F V) := by
    have := congrArg (fun u : (Module.End F V)ˣ => (u : Module.End F V)) hpq
    simpa [s16h_e3_z3f5_diagHom, s16h_e3_z3f5_diagUnit] using this
  obtain ⟨u, hu0, hu⟩ := s16h_e3_z3f5_exists_e_eq_zero hf5 hf1
  obtain ⟨w, hw0, hfw⟩ := s16h_e3_z3f5_exists_fixed hV hf5
  have hfkw : ∀ k : ℕ, ((f : Module.End F V) ^ k) w = w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [s16h_e3_z3f5_pow_apply_succ, ih, hfw]
  have hew : s16h_e3_z3f5_e (f : Module.End F V) w = w := by
    rw [s16h_e3_z3f5_e_apply, hfw, hfkw 2, hfkw 3, hfkw 4,
      s16h_e3_z3f5_add_self_eq_zero, zero_add, s16h_e3_z3f5_add_self_eq_zero, zero_add]
  have hp1 : p.1 = q.1 := by
    have h := congrFun (congrArg DFunLike.coe hval) u
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hu, sub_zero, smul_zero, add_zero] at h
    exact Units.ext (smul_left_injective F hu0 h)
  have hp2 : p.2 = q.2 := by
    have h := congrFun (congrArg DFunLike.coe hval) w
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hew, sub_self, smul_zero, zero_add] at h
    exact Units.ext (smul_left_injective F hw0 h)
  exact Prod.ext hp1 hp2

theorem s16h_e3_z3f5_unit_pow_three (x : Fˣ) : x ^ 3 = 1 := by
  apply Units.ext
  have h := s16h_e3_z3f5_cube_eq_zero_or_one (x : F)
  rcases h with h | h
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) (Units.ne_zero x)
  · simpa using h

theorem s16h_e3_z3f5_card_diagHom_range {f : (Module.End F V)ˣ}
    (hV : finrank F V = 3) (hf5 : (f : Module.End F V) ^ 5 = 1)
    (hf1 : (f : Module.End F V) ≠ 1) :
    Nat.card (s16h_e3_z3f5_diagHom (V := V) hf5).range = 9 := by
  have hinj := s16h_e3_z3f5_diagHom_injective hV hf5 hf1
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
    Nat.card_prod]
  have hcard : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, s16h_e3_z3f5_card_omegaField]
  rw [hcard]

theorem s16h_e3_z3f5_diagHom_pow_three {f : (Module.End F V)ˣ}
    (hf5 : (f : Module.End F V) ^ 5 = 1) (p : Fˣ × Fˣ) :
    (s16h_e3_z3f5_diagHom (V := V) hf5 p) ^ 3 = 1 := by
  have hp1 : p.1 ^ 3 = 1 := s16h_e3_z3f5_unit_pow_three p.1
  have hp2 : p.2 ^ 3 = 1 := s16h_e3_z3f5_unit_pow_three p.2
  have hp3 : p ^ 3 = 1 := by
    apply Prod.ext
    · change (MonoidHom.fst Fˣ Fˣ) (p ^ 3) = (MonoidHom.fst Fˣ Fˣ) 1
      rw [map_pow, map_one]
      exact hp1
    · change (MonoidHom.snd Fˣ Fˣ) (p ^ 3) = (MonoidHom.snd Fˣ Fˣ) 1
      rw [map_pow, map_one]
      exact hp2
  rw [← map_pow, hp3, map_one]

theorem s16h_e3_z3f5_diagHom_comm {f : (Module.End F V)ˣ}
    (hf5 : (f : Module.End F V) ^ 5 = 1) (p q : Fˣ × Fˣ) :
    s16h_e3_z3f5_diagHom (V := V) hf5 p * s16h_e3_z3f5_diagHom (V := V) hf5 q =
      s16h_e3_z3f5_diagHom (V := V) hf5 q * s16h_e3_z3f5_diagHom (V := V) hf5 p := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem s16h_e3_z3f5_three_element_mem {f : (Module.End F V)ˣ}
    (hV : finrank F V = 3) (hf5 : (f : Module.End F V) ^ 5 = 1)
    (hf1 : (f : Module.End F V) ≠ 1) {a : (Module.End F V)ˣ} (ha : a ^ 3 = 1)
    (hnorm : a * f * a⁻¹ ∈ Subgroup.zpowers f) :
    a ∈ (s16h_e3_z3f5_diagHom (V := V) hf5).range := by
  have hord : orderOf f = 5 := s16h_e3_z3f5_orderOf_eq_five hf5 hf1
  obtain ⟨α, μ, hα, hμ, haeq⟩ :=
    s16h_e3_z3f5_three_element_of_normalizes hV hord (m := 1) (by simpa using ha) hnorm
  have hα0 : α ≠ 0 := by rintro rfl; norm_num at hα
  have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at hμ
  refine MonoidHom.mem_range.mpr ⟨(Units.mk0 α hα0, Units.mk0 μ hμ0), ?_⟩
  apply Units.ext
  simpa [s16h_e3_z3f5_diagHom, s16h_e3_z3f5_diagUnit] using haeq.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

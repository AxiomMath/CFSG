module

public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartSlice

public section

namespace CFSG.StandardType.N2Chart

open Matrix Polynomial

noncomputable abbrev endo (g : SL6) : Module.End F4 V6 :=
  Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) F4)

theorem endo_apply (g : SL6) (v : V6) : endo g v = (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v :=
  Matrix.toLin'_apply _ _

theorem endo_pow (g : SL6) (k : ℕ) : endo (g ^ k) = endo g ^ k := by
  rw [endo, Matrix.SpecialLinearGroup.coe_pow, Matrix.toLin'_pow]

theorem endo_mul (g h : SL6) : endo (g * h) = endo g * endo h := by
  rw [endo, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
  rfl

theorem exists_omega : ∃ ω : F4, ω ^ 2 + ω + 1 = 0 := by
  classical
  let : Fintype F4 := Fintype.ofFinite F4
  have hcard : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h3 : 3 ∣ Fintype.card F4ˣ := by
    rw [Fintype.card_units, hcard]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 h3
  refine ⟨(g : F4), ?_⟩
  have hg3 : (g : F4) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  have hg1 : (g : F4) ≠ 1 := by
    intro h
    have : g = 1 := Units.val_eq_one.mp h
    rw [this, orderOf_one] at hg
    norm_num at hg
  have hmul : ((g : F4) - 1) * ((g : F4) ^ 2 + (g : F4) + 1) = 0 := by
    linear_combination hg3
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hg1)

noncomputable abbrev quadOm (c : F4) : F4[X] := X ^ 2 + C c * X + 1

theorem two_eq_zero_F4 : (2 : F4) = 0 := by
  have := CharP.cast_eq_zero F4 2
  exact_mod_cast this

theorem quadOm_mul_quadOm_sq {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) :
    quadOm ω * quadOm (ω ^ 2) = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  have h : C ω ^ 2 + C ω + 1 = (0 : F4[X]) := by
    rw [← C_pow, ← C_add, ← C_1, ← C_add, hω, C_0]
  have h2 : (2 : F4[X]) = 0 := by
    have := CharP.cast_eq_zero F4[X] 2
    exact_mod_cast this
  simp only [quadOm, C_pow]
  linear_combination (X ^ 3 + X + (C ω - 1) * X ^ 2) * h + (X ^ 2 - X ^ 3 - X) * h2

theorem quadOm_comp_sq {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) :
    (quadOm ω).comp (X ^ 2) = quadOm (ω ^ 2) ^ 2 := by
  have h : C ω ^ 2 + C ω + 1 = (0 : F4[X]) := by
    rw [← C_pow, ← C_add, ← C_1, ← C_add, hω, C_0]
  have h2 : (2 : F4[X]) = 0 := by
    have := CharP.cast_eq_zero F4[X] 2
    exact_mod_cast this
  simp only [quadOm, C_pow, add_comp, mul_comp, pow_comp, X_comp, C_comp, one_comp]
  linear_combination (-(C ω * (C ω - 1)) * X ^ 2) * h -
    (C ω ^ 2 * X ^ 3 + X ^ 2 + C ω ^ 2 * X) * h2

theorem aeval_quadOm_apply (c : F4) (f : Module.End F4 V6) (v : V6) :
    aeval f (quadOm c) v = f (f v) + c • f v + v := by
  simp only [quadOm, map_add, map_mul, aeval_X, aeval_C, map_one, LinearMap.add_apply, pow_two,
    Module.End.mul_apply, Module.algebraMap_end_apply, Module.End.one_apply]

theorem aeval_cyclo_suppSp {s : SL6} (hs : s ^ 5 = 1) {v : V6} (hv : v ∈ suppSp s) :
    aeval (endo s) (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : F4[X]) v = 0 := by
  obtain ⟨w, rfl⟩ := hv
  have h5 : endo s ^ 5 = 1 := by
    rw [← endo_pow, hs]
    simp [endo, Module.End.one_eq_id]
  have hfac : (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : F4[X]) * (X - 1) = X ^ 5 - 1 := by ring
  have hw : ((Matrix.toLin' (s : Matrix (Fin 6) (Fin 6) F4) - LinearMap.id : V6 →ₗ[F4] V6) w) =
      aeval (endo s) (X - 1 : F4[X]) w := by
    simp [endo]
  rw [hw, ← Module.End.mul_apply, ← map_mul, hfac, map_sub, map_pow, aeval_X, map_one, h5, sub_self,
    LinearMap.zero_apply]

theorem aeval_mem_suppSp {s : SL6} (p : F4[X]) {v : V6} (hv : v ∈ suppSp s) :
    aeval (endo s) p v ∈ suppSp s := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨aeval (endo s) p w, ?_⟩
  have key : ∀ u,
      ((Matrix.toLin' (s : Matrix (Fin 6) (Fin 6) F4) - LinearMap.id : V6 →ₗ[F4] V6) u) =
      aeval (endo s) (X - 1 : F4[X]) u := by
    intro u
    simp [endo]
  rw [key, key, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem quadOm_dichotomy {s : SL6} (hs : s ^ 5 = 1) (h2 : Module.finrank F4 (suppSp s) = 2)
    (hdisj : Disjoint (suppSp s) (fixSp s)) {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) :
    (∀ v ∈ suppSp s, aeval (endo s) (quadOm ω) v = 0) ∨
      (∀ v ∈ suppSp s, aeval (endo s) (quadOm (ω ^ 2)) v = 0) := by
  by_cases hq : ∀ v ∈ suppSp s, aeval (endo s) (quadOm ω) v = 0
  · exact Or.inl hq
  · right
    push Not at hq
    obtain ⟨v, hv, hw0⟩ := hq
    set w := aeval (endo s) (quadOm ω) v with hwdef
    have hwA : w ∈ suppSp s := aeval_mem_suppSp _ hv
    have hqw : aeval (endo s) (quadOm (ω ^ 2)) w = 0 := by
      rw [hwdef, ← Module.End.mul_apply, ← map_mul, mul_comm, quadOm_mul_quadOm_sq hω]
      exact aeval_cyclo_suppSp hs hv
    have hqsw : aeval (endo s) (quadOm (ω ^ 2)) ((s : Matrix (Fin 6) (Fin 6) F4) *ᵥ w) = 0 := by
      have e : (s : Matrix (Fin 6) (Fin 6) F4) *ᵥ w = aeval (endo s) (X : F4[X]) w := by
        rw [aeval_X, endo_apply]
      rw [e, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hqw,
        map_zero]
    intro u hu
    rw [← span_pair_eq_suppSp hs h2 hdisj hwA hw0] at hu
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hu
    rw [map_add, map_smul, map_smul, hqw, hqsw, smul_zero, smul_zero, add_zero]

theorem exists_quadOm_pow {s : SL6} (hs : s ^ 5 = 1) (h2 : Module.finrank F4 (suppSp s) = 2)
    (hdisj : Disjoint (suppSp s) (fixSp s)) {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ r : ℕ, (r = 1 ∨ r = 2) ∧ ∀ v ∈ suppSp s, aeval (endo (s ^ r)) (quadOm ω) v = 0 := by
  rcases quadOm_dichotomy hs h2 hdisj hω with h | h
  · exact ⟨1, Or.inl rfl, by simpa only [pow_one] using h⟩
  · refine ⟨2, Or.inr rfl, fun v hv => ?_⟩
    have e : endo (s ^ 2) = aeval (endo s) (X ^ 2 : F4[X]) := by
      rw [endo_pow, map_pow, aeval_X]
    rw [e, ← aeval_comp, quadOm_comp_sq hω, map_pow, pow_two, Module.End.mul_apply, h v hv,
      map_zero]

end CFSG.StandardType.N2Chart

end

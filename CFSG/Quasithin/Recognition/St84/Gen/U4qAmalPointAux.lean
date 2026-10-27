module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointSylow


public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

section Model

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem zRad_comm_radQ : ∀ z ∈ zRad h, ∀ x ∈ radQ h, z * x = x * z := fun z hz x hx =>
  ((mem_zRad_iff_comm h).mp hz).2 x hx

theorem zRad_sq_eq_one : ∀ z ∈ zRad h, z ^ 2 = 1 := by
  rintro z ⟨c, -, hz⟩
  apply hypSU_ext h
  rw [pow_two, coe_mul_hypSU, hz, sMat_mul_self_u4]
  simp only [map_zero, zero_mul, mul_zero, add_zero]
  exact sMat_zero_u4 h

theorem sq_mem_zRad_of_mem_radQ : ∀ x ∈ radQ h, x ^ 2 ∈ zRad h := by
  rintro g ⟨x, y, c, -, hg⟩
  refine ⟨h.bar y * x + h.bar x * y, ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, h.bar_bar, h.bar_bar, mul_comm y, mul_comm x, add_comm]
  · rw [pow_two, coe_mul_hypSU, hg, sMat_mul_self_u4]

theorem conj_mem_zRad_of_mem_normalizer : ∀ r ∈ Subgroup.normalizer (radQ h : Set (hypSU h 2 0)),
    ∀ z ∈ zRad h, r * z * r⁻¹ ∈ zRad h := by
  intro r hr z hz
  rw [mem_zRad_iff_comm] at hz ⊢
  have hzQ : r * z * r⁻¹ ∈ radQ h := (Subgroup.mem_normalizer_iff.mp hr z).mp hz.1
  refine ⟨hzQ, fun x hx => ?_⟩
  have hx' : r⁻¹ * x * r ∈ radQ h := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hr) x).mp hx
    simpa using this
  have hc := hz.2 _ hx'
  calc r * z * r⁻¹ * x = r * (z * (r⁻¹ * x * r)) * r⁻¹ := by group
    _ = r * ((r⁻¹ * x * r) * z) * r⁻¹ := by rw [hc]
    _ = x * (r * z * r⁻¹) := by group

end Model

theorem eq_zero_of_map_smul_eq_norm_mul {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (σ : K →+* K) {ω : K} (hω : σ ω ≠ ω) (ϕ : V →+ K)
    (hϕ : ∀ κ : K, κ ≠ 0 → ∀ v : V, ϕ (κ • v) = κ * σ κ * ϕ v) : ϕ = 0 := by
  ext v
  have hω0 : ω ≠ 0 := fun h0 => hω (by rw [h0, map_zero])
  have hω1 : 1 + ω ≠ 0 := by
    intro h1
    have : ω = 1 := by
      have := congrArg (· + 1) h1
      simp only [zero_add] at this
      rw [add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at this
      exact this
    exact hω (by rw [this, map_one])
  have h2 := hϕ ω hω0 v
  have h3 := hϕ (1 + ω) hω1 v
  rw [add_smul, one_smul, map_add, h2, map_add, map_one] at h3
  have hne : ω + σ ω ≠ 0 := by
    intro h0
    apply hω
    have := congrArg (· + σ ω) h0
    simp only [zero_add] at this
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at this
    exact this.symm
  have key : (ω + σ ω) * ϕ v = 0 := by linear_combination (-1 : K) * h3
  simpa using (mul_eq_zero.mp key).resolve_left hne

end CFSG.Quasithin.F112R.St84

end

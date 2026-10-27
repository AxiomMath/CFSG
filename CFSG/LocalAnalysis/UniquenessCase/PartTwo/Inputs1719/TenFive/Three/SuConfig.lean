module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.SuAniso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_hyp_partner (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {v w : HypIndex r ε → K} (hvw : hypForm h r ε v w = 0)
    (hw : w ∉ Submodule.span K {v}) (hww : hypForm h r ε w w = 0) :
    ∃ u : HypIndex r ε → K, hypForm h r ε v u = 0 ∧ hypForm h r ε w u = 1 ∧
      hypForm h r ε u u = 0 := by
  classical
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two hp2
  have hex : ∃ y, hypForm h r ε v y = 0 ∧ hypForm h r ε w y ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : LinearMap.ker (hypForm h r ε v) ≤ LinearMap.ker (hypForm h r ε w) := by
      intro y hy
      exact LinearMap.mem_ker.mpr (hcon y (LinearMap.mem_ker.mp hy))
    have hsp : hypForm h r ε w ∈ Submodule.span K {hypForm h r ε v} := by
      have h1 := mem_span_of_iInf_ker_le_ker (𝕜 := K) (E := HypIndex r ε → K) (ι := Unit)
        (L := fun _ => hypForm h r ε v) (K := hypForm h r ε w) (by simpa using hle)
      simpa using h1
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hsp
    apply hw
    have hz : w - h.bar lam • v = 0 := by
      apply hypForm_separatingLeft h
      intro y
      have h1 : hypForm h r ε (w - h.bar lam • v) y =
          hypForm h r ε w y - lam * hypForm h r ε v y := by
        rw [map_sub, map_smulₛₗ, UnitaryFieldData.bar_bar]
        simp
      rw [h1, ← hlam]
      simp
    exact Submodule.mem_span_singleton.mpr ⟨h.bar lam, (sub_eq_zero.mp hz).symm⟩
  obtain ⟨y, hyv, hyw⟩ := hex
  set u₀ : HypIndex r ε → K := (hypForm h r ε w y)⁻¹ • y with hu₀
  have hvu₀ : hypForm h r ε v u₀ = 0 := by
    rw [hu₀, map_smul, hyv, smul_zero]
  have hwu₀ : hypForm h r ε w u₀ = 1 := by
    rw [hu₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hyw]
  have hu₀w : hypForm h r ε u₀ w = 1 := by
    rw [← (hypForm_isSymm h).eq w u₀, hwu₀, map_one]
  set α : K := hypForm h r ε u₀ u₀ / 2 with hα
  have hbarα : h.bar α = α := by
    rw [hα, map_div₀, map_ofNat, (hypForm_isSymm h).eq u₀ u₀]
  refine ⟨u₀ - α • w, ?_, ?_, ?_⟩
  · simp only [map_sub, map_smul, smul_eq_mul, hvu₀, hvw, mul_zero, sub_zero]
  · simp only [map_sub, map_smul, smul_eq_mul, hwu₀, hww, mul_zero, sub_zero]
  · have hval : hypForm h r ε (u₀ - α • w) (u₀ - α • w) =
        hypForm h r ε u₀ u₀ - α * hypForm h r ε u₀ w - h.bar α * hypForm h r ε w u₀ +
          h.bar α * α * hypForm h r ε w w := by
      simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        map_smul, smul_eq_mul]
      ring
    simp only [hval, hu₀w, hwu₀, hww, hbarα]
    rw [hα]
    field_simp
    ring

theorem exists_heis_config (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hn : 4 ≤ 2 * r + ε)
    {v w₁ : HypIndex r ε → K} (hv0 : v ≠ 0) (h₁ : hypForm h r ε v w₁ = 0)
    (hw₁ : w₁ ∉ Submodule.span K {v}) :
    ∃ w₂ w₃ w₄ : HypIndex r ε → K, hypForm h r ε v w₂ = 0 ∧ hypForm h r ε v w₃ = 0 ∧
      hypForm h r ε v w₄ = 0 ∧ h.bar (hypForm h r ε w₁ w₂) ≠ hypForm h r ε w₁ w₂ ∧
      hypForm h r ε w₃ w₄ = hypForm h r ε w₁ w₂ ∧
      h.bar (hypForm h r ε w₁ w₃) = hypForm h r ε w₁ w₃ ∧
      h.bar (hypForm h r ε w₁ w₄) = hypForm h r ε w₁ w₄ ∧
      h.bar (hypForm h r ε w₂ w₃) = hypForm h r ε w₂ w₃ ∧
      h.bar (hypForm h r ε w₂ w₄) = hypForm h r ε w₂ w₄ := by
  classical
  obtain ⟨θ, hθ⟩ := h.exists_bar_ne
  by_cases hww : hypForm h r ε w₁ w₁ = 0
  ·
    obtain ⟨u, hvu, hwu, huu⟩ := exists_hyp_partner h hp2 h₁ hw₁ hww
    have huw₁ : hypForm h r ε u w₁ = 1 := by
      rw [← (hypForm_isSymm h).eq w₁ u, hwu, map_one]
    refine ⟨θ • u, u, θ • w₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [map_smul, smul_eq_mul, hvu, mul_zero]
    · exact hvu
    · simp only [map_smul, smul_eq_mul, h₁, mul_zero]
    · have hv12 : hypForm h r ε w₁ (θ • u) = θ := by
        simp only [map_smul, smul_eq_mul, hwu, mul_one]
      simp only [hv12]
      exact hθ
    · simp only [map_smul, smul_eq_mul, huw₁, hwu, mul_one]
    · simp only [hwu, map_one]
    · simp only [map_smul, smul_eq_mul, hww, mul_zero, map_zero]
    · simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, huu, smul_zero, map_zero]
    · have h24 : hypForm h r ε (θ • u) (θ • w₁) = θ * h.bar θ := by
        simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, huw₁,
          mul_one]
      rw [h24, map_mul, UnitaryFieldData.bar_bar]
      ring
  ·
    obtain ⟨y, hvy, hwy, hyy⟩ := exists_aniso_orth h hp2 hn hv0 h₁ hww
    set θ' : K := θ * hypForm h r ε w₁ w₁ / hypForm h r ε y y with hθ'
    have hbww : h.bar (hypForm h r ε w₁ w₁) = hypForm h r ε w₁ w₁ :=
      (hypForm_isSymm h).eq w₁ w₁
    refine ⟨θ • w₁, y, θ' • y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [map_smul, smul_eq_mul, h₁, mul_zero]
    · exact hvy
    · simp only [map_smul, smul_eq_mul, hvy, mul_zero]
    · have hv12 : hypForm h r ε w₁ (θ • w₁) = θ * hypForm h r ε w₁ w₁ := by
        rw [map_smul, smul_eq_mul]
      simp only [hv12, map_mul, hbww]
      intro hcon
      exact hθ (mul_right_cancel₀ hww hcon)
    · rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, hθ']
      field_simp
    · rw [hwy, map_zero]
    · simp only [map_smul, smul_eq_mul, hwy, mul_zero, map_zero]
    · simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hwy, smul_zero, map_zero]
    · simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, hwy, smul_zero,
        smul_zero, map_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuEichler
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Heis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] def heisVec (h : UnitaryFieldData p f K) (w₁ w₂ : HypIndex r ε → K)
    (x : Heis h.fixedField) : HypIndex r ε → K :=
  (x.a : K) • w₁ + (x.b : K) • w₂

@[expose] noncomputable def heisScalar (h : UnitaryFieldData p f K) (w₁ w₂ : HypIndex r ε → K)
    (x : Heis h.fixedField) : K :=
  -(hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₁ w₂ x) / 2) +
    ((x.a : K) * x.b - 2 * x.c) * ((hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) / 2)

private theorem heisVec_mul (h : UnitaryFieldData p f K) (w₁ w₂ : HypIndex r ε → K)
    (x y : Heis h.fixedField) :
    heisVec h w₁ w₂ (x * y) = heisVec h w₁ w₂ x + heisVec h w₁ w₂ y := by
  simp only [heisVec, Heis.mul_a, Heis.mul_b, Subfield.coe_add, add_smul]
  abel

private theorem hypForm_heisVec_heisVec (h : UnitaryFieldData p f K)
    (w₁ w₂ : HypIndex r ε → K) (x y : Heis h.fixedField) :
    hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₁ w₂ y) =
      (x.a : K) * (y.a : K) * hypForm h r ε w₁ w₁ +
        (x.a : K) * (y.b : K) * hypForm h r ε w₁ w₂ +
        (x.b : K) * (y.a : K) * h.bar (hypForm h r ε w₁ w₂) +
        (x.b : K) * (y.b : K) * hypForm h r ε w₂ w₂ := by
  have ha : h.bar (x.a : K) = (x.a : K) := h.mem_fixedField.mp x.a.2
  have hb : h.bar (x.b : K) = (x.b : K) := h.mem_fixedField.mp x.b.2
  have h21 : hypForm h r ε w₂ w₁ = h.bar (hypForm h r ε w₁ w₂) :=
    ((hypForm_isSymm h).eq w₁ w₂).symm
  simp only [heisVec, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, ha, hb, h21]
  ring

private theorem hypForm_single_heisVec (h : UnitaryFieldData p f K)
    (z w₁ w₂ : HypIndex r ε → K) (x : Heis h.fixedField) :
    hypForm h r ε z (heisVec h w₁ w₂ x) =
      (x.a : K) * hypForm h r ε z w₁ + (x.b : K) * hypForm h r ε z w₂ := by
  simp only [heisVec, map_add, map_smul, smul_eq_mul]

private theorem heisScalar_mul (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (w₁ w₂ : HypIndex r ε → K) (x y : Heis h.fixedField) :
    heisScalar h w₁ w₂ (x * y) =
      heisScalar h w₁ w₂ x + heisScalar h w₁ w₂ y -
        hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₁ w₂ y) := by
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  simp only [heisScalar]
  rw [hypForm_heisVec_heisVec h w₁ w₂ (x * y) (x * y),
    hypForm_heisVec_heisVec h w₁ w₂ x x,
    hypForm_heisVec_heisVec h w₁ w₂ y y,
    hypForm_heisVec_heisVec h w₁ w₂ x y]
  simp only [Heis.mul_a, Heis.mul_b, Heis.mul_c, Subfield.coe_add, Subfield.coe_mul]
  field_simp
  ring

theorem hypForm_heisVec (h : UnitaryFieldData p f K) {v w₁ w₂ : HypIndex r ε → K}
    (h₁ : hypForm h r ε v w₁ = 0) (h₂ : hypForm h r ε v w₂ = 0) (x : Heis h.fixedField) :
    hypForm h r ε v (heisVec h w₁ w₂ x) = 0 := by
  simp only [heisVec, map_add, map_smul, smul_eq_mul, h₁, h₂, mul_zero, add_zero]

theorem heisScalar_trace (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (w₁ w₂ : HypIndex r ε → K)
    (x : Heis h.fixedField) :
    heisScalar h w₁ w₂ x + h.bar (heisScalar h w₁ w₂ x) +
      hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₁ w₂ x) = 0 := by
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hX : h.bar (hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₁ w₂ x)) =
      hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₁ w₂ x) :=
    (hypForm_isSymm h).eq _ _
  have hY : h.bar ((x.a : K) * x.b - 2 * x.c) = (x.a : K) * x.b - 2 * x.c := by
    rw [map_sub, map_mul, map_mul, map_ofNat, h.mem_fixedField.mp x.a.2,
      h.mem_fixedField.mp x.b.2, h.mem_fixedField.mp x.c.2]
  have ht : h.bar ((hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) / 2) =
      -((hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) / 2) := by
    rw [map_div₀, map_sub, h.bar_bar, map_ofNat]
    ring
  have hsum : h.bar (-(hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₁ w₂ x) / 2) +
      ((x.a : K) * x.b - 2 * x.c) *
        ((hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) / 2)) =
      -(hypForm h r ε (heisVec h w₁ w₂ x) (heisVec h w₁ w₂ x) / 2) +
        ((x.a : K) * x.b - 2 * x.c) *
          -((hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) / 2) := by
    rw [map_add, map_neg, map_div₀, map_ofNat, hX, map_mul, hY, ht]
  simp only [heisScalar]
  rw [hsum]
  field_simp
  ring

private noncomputable def heisSUFun (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {v w₁ w₂ : HypIndex r ε → K} (hv : hypForm h r ε v v = 0)
    (h₁ : hypForm h r ε v w₁ = 0) (h₂ : hypForm h r ε v w₂ = 0)
    (x : Heis h.fixedField) : hypSU h r ε :=
  eichlerSU h hv (hypForm_heisVec h h₁ h₂ x) (heisScalar_trace h hp2 w₁ w₂ x)

private theorem heisSUFun_mul (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {v w₁ w₂ : HypIndex r ε → K} (hv : hypForm h r ε v v = 0)
    (h₁ : hypForm h r ε v w₁ = 0) (h₂ : hypForm h r ε v w₂ = 0) (x y : Heis h.fixedField) :
    heisSUFun h hp2 hv h₁ h₂ (x * y) = heisSUFun h hp2 hv h₁ h₂ x * heisSUFun h hp2 hv h₁ h₂ y := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Units.val_mul, heisSUFun, heisSUFun, heisSUFun, coe_eichlerSU,
    coe_eichlerSU, coe_eichlerSU,
    hypEichler_mul h (heisScalar h w₁ w₂ x) (heisScalar h w₁ w₂ y) hv
      (hypForm_heisVec h h₁ h₂ x) (hypForm_heisVec h h₁ h₂ y),
    heisVec_mul, heisScalar_mul h hp2]

private noncomputable def heisSUHom (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {v w₁ w₂ : HypIndex r ε → K} (hv : hypForm h r ε v v = 0)
    (h₁ : hypForm h r ε v w₁ = 0) (h₂ : hypForm h r ε v w₂ = 0) :
    Heis h.fixedField →* hypSU h r ε :=
  MonoidHom.mk' (heisSUFun h hp2 hv h₁ h₂) (heisSUFun_mul h hp2 hv h₁ h₂)

private theorem heis_eq_one_of_hypProj_eq_one (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {v w₁ w₂ : HypIndex r ε → K} (hv0 : v ≠ 0) (hv : hypForm h r ε v v = 0)
    (h₁ : hypForm h r ε v w₁ = 0) (h₂ : hypForm h r ε v w₂ = 0)
    (hω : h.bar (hypForm h r ε w₁ w₂) ≠ hypForm h r ε w₁ w₂)
    {x : Heis h.fixedField}
    (hx : hypProj h r ε (heisSUFun h hp2 hv h₁ h₂ x) = 1) : x = 1 := by
  classical
  have : CharP K p := h.charP
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  set W := heisVec h w₁ w₂ x with hWdef
  set Γ := heisScalar h w₁ w₂ x with hΓdef
  set E := heisSUFun h hp2 hv h₁ h₂ x with hEdef
  have hWorth : hypForm h r ε v W = 0 := hypForm_heisVec h h₁ h₂ x
  have hWorth' : hypForm h r ε W v = 0 := by
    rw [← (hypForm_isSymm h).eq v W, hWorth, map_zero]
  have hmem : E ∈ hypScalars h r ε := by
    rw [← ker_hypProj]
    exact MonoidHom.mem_ker.mpr hx
  obtain ⟨μ, -, -, hμ⟩ := mem_normOneScalars.mp hmem
  have hmat : ((E : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (μ : K) • 1 := by
    rw [hμ, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal]
  have hEmat : ((E : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      hypEichler h v W Γ := by
    rw [hEdef, heisSUFun, coe_eichlerSU, ← hWdef, ← hΓdef]
  have hEv : ((E : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v =
      v := by
    rw [hEmat, hypEichler_mulVec, hv, hWorth']
    simp
  have hμ1 : μ = 1 := by
    have h1 : (μ : K) • v = v := by
      have h := hEv
      rw [hmat, smul_mulVec, one_mulVec] at h
      exact h
    have h2 : (μ : K) • v = ((1 : Kˣ) : K) • v := by
      rw [h1, Units.val_one, one_smul]
    exact Units.ext ((smul_left_inj hv0).mp h2)
  have hmat1 : ((E : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [hmat, hμ1]
    simp
  have hEfix : ∀ y : HypIndex r ε → K,
      ((E : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y = y := by
    intro y
    rw [hmat1, one_mulVec]
  obtain ⟨y, hy⟩ : ∃ y : HypIndex r ε → K, hypForm h r ε v y = 1 := by
    have hex : ∃ y : HypIndex r ε → K, hypForm h r ε v y ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv0 ((hypForm_separatingLeft h) v hc)
    obtain ⟨y, hy⟩ := hex
    exact ⟨(hypForm h r ε v y)⁻¹ • y, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  have hWrel : W = (hypForm h r ε W y - Γ) • v := by
    have h1 : hypEichler h v W Γ *ᵥ y = y := by
      rw [← hEmat]
      exact hEfix y
    rw [hypEichler_mulVec, hy] at h1
    simp only [one_smul, mul_one] at h1
    have h1' : y + (W - hypForm h r ε W y • v + Γ • v) = y := by
      rw [show y + (W - hypForm h r ε W y • v + Γ • v) =
        y + W - hypForm h r ε W y • v + Γ • v from by abel]
      exact h1
    have h2 : W - hypForm h r ε W y • v + Γ • v = 0 := by
      have h4 := congrArg (fun z => z - y) h1'
      rwa [add_sub_cancel_left, sub_self] at h4
    calc W = (W - hypForm h r ε W y • v) + hypForm h r ε W y • v := by abel
      _ = -(Γ • v) + hypForm h r ε W y • v := by
          rw [eq_neg_of_add_eq_zero_left h2]
      _ = (hypForm h r ε W y - Γ) • v := by
          rw [sub_smul]; abel
  have hb0 : (x.b : K) = 0 := by
    have hw1v : hypForm h r ε w₁ v = 0 := by
      rw [← (hypForm_isSymm h).eq v w₁, h₁, map_zero]
    have hw1W : hypForm h r ε w₁ W = 0 := by
      rw [hWrel, map_smul, hw1v, smul_zero]
    have hz : (x.a : K) * hypForm h r ε w₁ w₁ +
        (x.b : K) * hypForm h r ε w₁ w₂ = 0 := by
      rw [← hypForm_single_heisVec h w₁ w₁ w₂ x, ← hWdef]
      exact hw1W
    have hzb : (x.a : K) * hypForm h r ε w₁ w₁ +
        (x.b : K) * h.bar (hypForm h r ε w₁ w₂) = 0 := by
      have hbar := congrArg h.bar hz
      rw [map_add, map_mul, map_mul, map_zero, h.mem_fixedField.mp x.a.2,
        (hypForm_isSymm h).eq w₁ w₁, h.mem_fixedField.mp x.b.2] at hbar
      exact hbar
    have hsub : (x.b : K) * (hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) = 0 := by
      linear_combination hz - hzb
    exact (mul_eq_zero.mp hsub).resolve_right (sub_ne_zero.mpr (Ne.symm hω))
  have hW2 : W = (x.a : K) • w₁ := by
    rw [hWdef]
    simp only [heisVec, hb0, zero_smul, add_zero]
  have ha0 : (x.a : K) = 0 := by
    have hWw2 : hypForm h r ε W w₂ = 0 := by
      rw [hWrel, map_smulₛₗ, LinearMap.smul_apply, h₂, smul_zero]
    have hWa : hypForm h r ε W w₂ = (x.a : K) * hypForm h r ε w₁ w₂ := by
      rw [hW2, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        h.mem_fixedField.mp x.a.2]
    have hO0 : hypForm h r ε w₁ w₂ ≠ 0 := by
      intro hO
      exact hω (by rw [hO, map_zero])
    rw [hWa] at hWw2
    exact (mul_eq_zero.mp hWw2).resolve_right hO0
  have hW0 : W = 0 := by
    rw [hW2, ha0, zero_smul]
  have hΓ0 : Γ = 0 := by
    have h1 : hypEichler h v W Γ *ᵥ y = y := by
      rw [← hEmat]
      exact hEfix y
    rw [hypEichler_mulVec, hy, hW0] at h1
    simp only [map_zero, mul_one] at h1
    have h2 : y + Γ • v = y := by simpa using h1
    have h3 : y + Γ • v = y + 0 := by rw [h2, add_zero]
    have h4 : Γ • v = 0 := add_left_cancel h3
    exact (smul_eq_zero.mp h4).resolve_right hv0
  have ht : ((hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) / 2) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (Ne.symm hω)) h2K
  have hc0 : (x.c : K) = 0 := by
    have hsc : Γ = (x.c : K) * (-(2 : K) *
        ((hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) / 2)) := by
      rw [hΓdef]
      simp only [heisScalar, ← hWdef, hW0, ha0, hb0, map_zero, zero_div,
        mul_zero, neg_zero]
      ring
    rw [hsc] at hΓ0
    exact (mul_eq_zero.mp hΓ0).resolve_right (mul_ne_zero (neg_ne_zero.mpr h2K) ht)
  have ha' : x.a = 0 := Subtype.ext ha0
  have hb' : x.b = 0 := Subtype.ext hb0
  have hc' : x.c = 0 := Subtype.ext hc0
  ext <;> simp [ha', hb', hc']

theorem exists_heis_hypPSU (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {v w₁ w₂ : HypIndex r ε → K} (hv0 : v ≠ 0) (hv : hypForm h r ε v v = 0)
    (h₁ : hypForm h r ε v w₁ = 0) (h₂ : hypForm h r ε v w₂ = 0)
    (hω : h.bar (hypForm h r ε w₁ w₂) ≠ hypForm h r ε w₁ w₂) :
    ∃ ι : Heis h.fixedField →* hypPSU h r ε, Function.Injective ι ∧ ∀ x,
      ι x = hypProj h r ε (eichlerSU h hv (hypForm_heisVec h h₁ h₂ x)
        (heisScalar_trace h hp2 w₁ w₂ x)) := by
  classical
  refine ⟨(hypProj h r ε).comp (heisSUHom h hp2 hv h₁ h₂), ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    simp only [MonoidHom.comp_apply] at hx
    exact heis_eq_one_of_hypProj_eq_one h hp2 hv0 hv h₁ h₂ hω hx
  · intro x
    simp only [MonoidHom.comp_apply, heisSUHom, MonoidHom.mk'_apply, heisSUFun]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

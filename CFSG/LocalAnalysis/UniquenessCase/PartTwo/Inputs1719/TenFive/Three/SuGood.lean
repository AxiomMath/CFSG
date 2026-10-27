module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.SuPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.SuConfig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)

variable {K : Type} [Field K] {r ε : ℕ}

private theorem eichlerSU_congr {p f : ℕ} (h : UnitaryFieldData p f K)
    {v v' w w' : HypIndex r ε → K} {γ γ' : K}
    (hv : v = v') (hw : w = w') (hγ : γ = γ')
    (p1 : hypForm h r ε v v = 0) (p2 : hypForm h r ε v w = 0)
    (p3 : γ + h.bar γ + hypForm h r ε w w = 0)
    (q1 : hypForm h r ε v' v' = 0) (q2 : hypForm h r ε v' w' = 0)
    (q3 : γ' + h.bar γ' + hypForm h r ε w' w' = 0) :
    eichlerSU h p1 p2 p3 = eichlerSU h q1 q2 q3 := by
  subst hv hw hγ
  exact Subtype.ext (Units.ext rfl)

private theorem exists_orthogonal_notMem_span {p f : ℕ} (h : UnitaryFieldData p f K)
    {v : HypIndex r ε → K} (hv : v ≠ 0) (hn : 3 ≤ 2 * r + ε) :
    ∃ w₁, hypForm h r ε v w₁ = 0 ∧ w₁ ∉ Submodule.span K {v} := by
  have hf : hypForm h r ε v ≠ 0 := by
    intro h0
    exact hv (hypForm_separatingLeft h v (by simp [h0]))
  have hfr : Module.finrank K (LinearMap.range (hypForm h r ε v)) = 1 := by
    rw [Module.Dual.range_eq_top_of_ne_zero hf, finrank_top, Module.finrank_self]
  have hdim : Module.finrank K (HypIndex r ε → K) = 2 * r + ε := finrank_hypIndex_fun
  have hker : Module.finrank K (LinearMap.ker (hypForm h r ε v)) = 2 * r + ε - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker (hypForm h r ε v)
    rw [hfr, hdim] at hsum
    omega
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle : LinearMap.ker (hypForm h r ε v) ≤ Submodule.span K {v} := by
    intro y hy
    exact hcon y (LinearMap.mem_ker.mp hy)
  have hle1 : Module.finrank K (LinearMap.ker (hypForm h r ε v)) ≤
      Module.finrank K (Submodule.span K {v}) := Submodule.finrank_mono hle
  rw [hker, finrank_span_singleton hv] at hle1
  omega

private theorem isExtraGood_of_heis_config (h : UnitaryFieldData 3 1 K)
    {v w : HypIndex r ε → K} {γ : K} (hd : IsEichlerDatum h v w γ)
    {w₁ w₂ w₃ w₄ : HypIndex r ε → K}
    (h₁ : hypForm h r ε v w₁ = 0) (h₂ : hypForm h r ε v w₂ = 0)
    (h₃ : hypForm h r ε v w₃ = 0) (h₄ : hypForm h r ε v w₄ = 0)
    (hω : h.bar (hypForm h r ε w₁ w₂) ≠ hypForm h r ε w₁ w₂)
    (hω' : hypForm h r ε w₃ w₄ = hypForm h r ε w₁ w₂)
    (h13 : h.bar (hypForm h r ε w₁ w₃) = hypForm h r ε w₁ w₃)
    (h14 : h.bar (hypForm h r ε w₁ w₄) = hypForm h r ε w₁ w₄)
    (h23 : h.bar (hypForm h r ε w₂ w₃) = hypForm h r ε w₂ w₃)
    (h24 : h.bar (hypForm h r ε w₂ w₄) = hypForm h r ε w₂ w₄)
    (x : Heis h.fixedField) (hvec : heisVec h w₁ w₂ x = w) (hsc : heisScalar h w₁ w₂ x = γ)
    (hx1 : x ≠ 1) :
    orderOf (hypProj h r ε (eichlerSU h hd.isotropic hd.orthogonal hd.trace_eq)) = 3 ∧
      IsExtraGood (hypProj h r ε (eichlerSU h hd.isotropic hd.orthogonal hd.trace_eq)) := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hF : Nat.card h.fixedField = 3 := by simpa using h.card_fixedField
  obtain ⟨ι₁, ι₂, hι₁, hι₂, hcomm, hcen, hι₁x⟩ :=
    exists_heis_pair_hypPSU h hp2 hd.ne_zero hd.isotropic h₁ h₂ h₃ h₄ hω hω' h13 h14 h23 h24
  have hAx : hypProj h r ε (eichlerSU h hd.isotropic hd.orthogonal hd.trace_eq) = ι₁ x := by
    rw [hι₁x x]
    exact congrArg (hypProj h r ε)
      (eichlerSU_congr h rfl hvec.symm hsc.symm hd.isotropic hd.orthogonal hd.trace_eq
        hd.isotropic (hypForm_heisVec h h₁ h₂ x) (heisScalar_trace h hp2 w₁ w₂ x))
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : CharP K 3 := h.charP
  have : Finite K := h.finite
  have : CharP h.fixedField 3 := Subfield.charP h.fixedField 3
  have : Finite h.fixedField := inferInstance
  have hordx : orderOf x = 3 :=
    orderOf_eq_prime (Heis.pow_prime_eq_one (p := 3) (by norm_num) hp2 x) hx1
  exact ⟨by rw [hAx]; exact (orderOf_injective ι₁ hι₁ x).trans hordx,
    by rw [hAx]; exact isExtraGood_of_heis_pair hF hι₁ hι₂ hcomm hcen x⟩

theorem isExtraGood_eichlerSU_three (h : UnitaryFieldData 3 1 K) (hn : 4 ≤ 2 * r + ε)
    {v w : HypIndex r ε → K} {γ : K} (hd : IsEichlerDatum h v w γ) :
    orderOf (hypProj h r ε (eichlerSU h hd.isotropic hd.orthogonal hd.trace_eq)) = 3 ∧
      IsExtraGood (hypProj h r ε (eichlerSU h hd.isotropic hd.orthogonal hd.trace_eq)) := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : CharP K 3 := h.charP
  have : Finite K := h.finite
  have : CharP h.fixedField 3 := Subfield.charP h.fixedField 3
  have : Finite h.fixedField := inferInstance
  have h2 : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two hp2
  rcases hd.nontrivial with hw | ⟨hw0, hγ0⟩
  ·
    obtain ⟨w₂, w₃, w₄, h₂, h₃, h₄, hω, hω', h13, h14, h23, h24⟩ :=
      exists_heis_config h hp2 hn hd.ne_zero hd.orthogonal hw
    have hbww : h.bar (hypForm h r ε w w) = hypForm h r ε w w :=
      (LinearMap.isSymm_def.mp (hypForm_isSymm h)) w w
    set om : K := hypForm h r ε w w₂ with hom
    set t : K := (om - h.bar om) / 2 with ht
    set qq : K := γ + hypForm h r ε w w / 2 with hqq
    have hbart : h.bar t = -t := by
      rw [ht, map_div₀, map_sub, UnitaryFieldData.bar_bar, map_ofNat]
      ring_nf
    have ht0 : t ≠ 0 := by
      rw [ht]
      exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hω)) h2
    have hbarqq : h.bar qq = -qq := by
      have h1 : h.bar γ = -γ - hypForm h r ε w w := by linear_combination hd.trace_eq
      rw [hqq, map_add, map_div₀, hbww, map_ofNat, h1]
      field_simp
      ring
    set c : K := -qq / (2 * t) with hc
    have hbarc : h.bar c = c := by
      rw [hc, map_div₀, map_mul, map_neg, hbarqq, hbart, map_ofNat, neg_neg]
      field_simp
    have hcmem : c ∈ h.fixedField := h.mem_fixedField.mpr hbarc
    have hvec : heisVec h w w₂ ⟨1, 0, ⟨c, hcmem⟩⟩ = w := by simp [heisVec]
    have hsc : heisScalar h w w₂ ⟨1, 0, ⟨c, hcmem⟩⟩ = γ := by
      have ht2 : (hypForm h r ε w w₂ - h.bar (hypForm h r ε w w₂)) / 2 = t := by
        rw [ht, hom]
      have h2ct : 2 * c * t = -qq := by
        rw [hc]
        field_simp
      simp only [heisScalar, hvec, Subfield.coe_one, Subfield.coe_zero]
      rw [ht2]
      rw [show (1 : K) * 0 - 2 * c = -(2 * c) by ring, neg_mul, h2ct, neg_neg, hqq]
      ring
    have hx1 : (⟨1, 0, ⟨c, hcmem⟩⟩ : Heis h.fixedField) ≠ 1 := by
      intro hx1
      have ha : ((1 : h.fixedField) : K) = 0 := by simpa using congrArg Heis.a hx1
      exact one_ne_zero ha
    exact isExtraGood_of_heis_config h hd hd.orthogonal h₂ h₃ h₄ hω hω' h13 h14 h23 h24
      ⟨1, 0, ⟨c, hcmem⟩⟩ hvec hsc hx1
  ·
    obtain ⟨w₁, h₁, hw₁⟩ := exists_orthogonal_notMem_span h hd.ne_zero (by omega)
    obtain ⟨w₂, w₃, w₄, h₂, h₃, h₄, hω, hω', h13, h14, h23, h24⟩ :=
      exists_heis_config h hp2 hn hd.ne_zero h₁ hw₁
    have hbarg : h.bar γ = -γ := by
      have htr := hd.trace_eq
      rw [hw0] at htr
      simp only [map_zero, add_zero] at htr
      linear_combination htr
    set om : K := hypForm h r ε w₁ w₂ with hom
    set t : K := (om - h.bar om) / 2 with ht
    have hbart : h.bar t = -t := by
      rw [ht, map_div₀, map_sub, UnitaryFieldData.bar_bar, map_ofNat]
      ring_nf
    have ht0 : t ≠ 0 := by
      rw [ht]
      exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hω)) h2
    set c : K := -γ / (2 * t) with hc
    have hbarc : h.bar c = c := by
      rw [hc, map_div₀, map_mul, map_neg, hbarg, hbart, map_ofNat, neg_neg]
      field_simp
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact div_ne_zero (neg_ne_zero.mpr hγ0) (mul_ne_zero h2 ht0)
    have hcmem : c ∈ h.fixedField := h.mem_fixedField.mpr hbarc
    have hww0 : hypForm h r ε w w = 0 := by rw [hw0]; simp
    have hvec : heisVec h w₁ w₂ ⟨0, 0, ⟨c, hcmem⟩⟩ = w := by
      rw [hw0]
      simp [heisVec]
    have hsc : heisScalar h w₁ w₂ ⟨0, 0, ⟨c, hcmem⟩⟩ = γ := by
      have ht2 : (hypForm h r ε w₁ w₂ - h.bar (hypForm h r ε w₁ w₂)) / 2 = t := by
        rw [ht, hom]
      have h2ct : 2 * c * t = -γ := by
        rw [hc]
        field_simp
      simp only [heisScalar, hvec, hww0, Subfield.coe_zero]
      rw [ht2]
      rw [show (0 : K) * 0 - 2 * c = -(2 * c) by ring, neg_mul, h2ct, neg_neg]
      ring
    have hx1 : (⟨0, 0, ⟨c, hcmem⟩⟩ : Heis h.fixedField) ≠ 1 := by
      intro hx1
      have h1 : (⟨c, hcmem⟩ : h.fixedField) = 0 := by simpa using congrArg Heis.c hx1
      have hcz : c = 0 := by simpa using congrArg (fun y : h.fixedField => (y : K)) h1
      exact hc0 hcz
    exact isExtraGood_of_heis_config h hd h₁ h₂ h₃ h₄ hω hω' h13 h14 h23 h24
      ⟨0, 0, ⟨c, hcmem⟩⟩ hvec hsc hx1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

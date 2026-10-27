module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuHeisHom
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Heis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private theorem eichlerSU_congr (h : UnitaryFieldData p f K)
    {v v' w w' : HypIndex r ε → K} {γ γ' : K}
    (hv : v = v') (hw : w = w') (hγ : γ = γ')
    (p1 : hypForm h r ε v v = 0) (p2 : hypForm h r ε v w = 0)
    (p3 : γ + h.bar γ + hypForm h r ε w w = 0)
    (q1 : hypForm h r ε v' v' = 0) (q2 : hypForm h r ε v' w' = 0)
    (q3 : γ' + h.bar γ' + hypForm h r ε w' w' = 0) :
    eichlerSU h p1 p2 p3 = eichlerSU h q1 q2 q3 := by
  subst hv hw hγ
  exact Subtype.ext (Units.ext rfl)

private theorem exists_partner (h : UnitaryFieldData p f K) {v w : HypIndex r ε → K}
    (hw : w ∉ Submodule.span K {v}) :
    ∃ w₂, hypForm h r ε v w₂ = 0 ∧ h.bar (hypForm h r ε w w₂) ≠ hypForm h r ε w w₂ := by
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
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  refine ⟨(c / hypForm h r ε w y) • y, ?_, ?_⟩
  · rw [map_smul, hyv, smul_zero]
  · have hval : hypForm h r ε w ((c / hypForm h r ε w y) • y) = c := by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hyw]
    rw [hval]
    exact hc

private theorem exists_orthogonal_notMem_span (h : UnitaryFieldData p f K)
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

private theorem good_of_heis (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h3 : 3 < p ^ f)
    {v w : HypIndex r ε → K} {γ : K} (hv0 : v ≠ 0) (hv : hypForm h r ε v v = 0)
    (hvw : hypForm h r ε v w = 0) (hγ : γ + h.bar γ + hypForm h r ε w w = 0)
    {w₁ w₂ : HypIndex r ε → K} (h₁ : hypForm h r ε v w₁ = 0) (h₂ : hypForm h r ε v w₂ = 0)
    (hω : h.bar (hypForm h r ε w₁ w₂) ≠ hypForm h r ε w₁ w₂) (x : Heis h.fixedField)
    (hvec : heisVec h w₁ w₂ x = w) (hsc : heisScalar h w₁ w₂ x = γ) (hx1 : x ≠ 1) :
    orderOf (hypProj h r ε (eichlerSU h hv hvw hγ)) = p ∧
      IsSpecialGood p (hypProj h r ε (eichlerSU h hv hvw hγ)) := by
  obtain ⟨ι, hι_inj, hι⟩ := exists_heis_hypPSU h hp2 hv0 hv h₁ h₂ hω
  have hAx : hypProj h r ε (eichlerSU h hv hvw hγ) = ι x := by
    rw [hι x]
    exact congrArg (hypProj h r ε) (eichlerSU_congr h rfl hvec.symm hsc.symm hv hvw hγ hv
      (hypForm_heisVec h h₁ h₂ x) (heisScalar_trace h hp2 w₁ w₂ x))
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Finite K := h.finite
  have : CharP h.fixedField p := Subfield.charP h.fixedField p
  have : Finite h.fixedField := inferInstance
  have hordx : orderOf x = p :=
    orderOf_eq_prime (Heis.pow_prime_eq_one h.prime hp2 x) hx1
  refine ⟨?_, ?_⟩
  · rw [hAx]
    exact (orderOf_injective ι hι_inj x).trans hordx
  · rw [hAx]
    exact isSpecialGood_of_heis h.prime hp2 h.card_fixedField h3 hι_inj x

theorem good_eichlerSU (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h3 : 3 < p ^ f)
    (hn : 3 ≤ 2 * r + ε) {v w : HypIndex r ε → K} {γ : K} (hd : IsEichlerDatum h v w γ) :
    orderOf (hypProj h r ε (eichlerSU h hd.isotropic hd.orthogonal hd.trace_eq)) = p ∧
      IsSpecialGood p (hypProj h r ε (eichlerSU h hd.isotropic hd.orthogonal hd.trace_eq)) := by
  classical
  have := h.charP
  have h2 : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two hp2
  rcases hd.nontrivial with hw | ⟨hw0, hγ0⟩
  ·
    obtain ⟨w₂, h₂, hω⟩ := exists_partner h hw
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
    refine good_of_heis h hp2 h3 hd.ne_zero hd.isotropic hd.orthogonal hd.trace_eq
      hd.orthogonal h₂ hω ⟨1, 0, ⟨c, hcmem⟩⟩ hvec hsc ?_
    intro hx1
    have ha : ((1 : h.fixedField) : K) = 0 := by simpa using congrArg Heis.a hx1
    exact one_ne_zero ha
  ·
    obtain ⟨w₁, h₁, hw₁⟩ := exists_orthogonal_notMem_span h hd.ne_zero hn
    obtain ⟨w₂, h₂, hω⟩ := exists_partner h hw₁
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
    refine good_of_heis h hp2 h3 hd.ne_zero hd.isotropic hd.orthogonal hd.trace_eq
      h₁ h₂ hω ⟨0, 0, ⟨c, hcmem⟩⟩ hvec hsc ?_
    intro hx1
    have h1 : (⟨c, hcmem⟩ : h.fixedField) = 0 := by simpa using congrArg Heis.c hx1
    have hcz : c = 0 := by simpa using congrArg (fun y : h.fixedField => (y : K)) h1
    exact hc0 hcz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

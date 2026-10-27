module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflProductOrder
public import CFSG.LocalAnalysis.StandardType.ZS.Basic

public section

namespace CFSG.StandardType.ZS

open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

local instance (priority := high) zsix_zmodAddCommGroup : AddCommGroup (ZMod p) :=
  Ring.toAddCommGroup

private theorem zsix_field_core (hp : p ≠ 2) {P Q : ZMod p}
    (hP : P + P⁻¹ = 1) (hQ : Q + Q⁻¹ = 1) (hPQ : P * Q⁻¹ + Q * P⁻¹ = 0) : False := by
  have hP0 : P ≠ 0 := by rintro rfl; rw [inv_zero, add_zero] at hP; exact zero_ne_one hP
  have hQ0 : Q ≠ 0 := by rintro rfl; rw [inv_zero, add_zero] at hQ; exact zero_ne_one hQ
  have hP2 : P ^ 2 = P - 1 := by
    have h : P * P + 1 = P := by
      calc P * P + 1 = P * P + P * P⁻¹ := by rw [mul_inv_cancel₀ hP0]
        _ = (P + P⁻¹) * P := by ring
        _ = 1 * P := by rw [hP]
        _ = P := by ring
    rw [pow_two]
    linear_combination h
  have hQ2 : Q ^ 2 = Q - 1 := by
    have h : Q * Q + 1 = Q := by
      calc Q * Q + 1 = Q * Q + Q * Q⁻¹ := by rw [mul_inv_cancel₀ hQ0]
        _ = (Q + Q⁻¹) * Q := by ring
        _ = 1 * Q := by rw [hQ]
        _ = Q := by ring
    rw [pow_two]
    linear_combination h
  have hsum : P ^ 2 + Q ^ 2 = 0 := by
    have h : (P * Q⁻¹ + Q * P⁻¹) * (P * Q) = 0 := by rw [hPQ, zero_mul]
    rw [add_mul] at h
    have e1 : P * Q⁻¹ * (P * Q) = P ^ 2 := by
      calc P * Q⁻¹ * (P * Q) = (P * P) * (Q⁻¹ * Q) := by ring
        _ = P ^ 2 := by rw [inv_mul_cancel₀ hQ0, mul_one, pow_two]
    have e2 : Q * P⁻¹ * (P * Q) = Q ^ 2 := by
      calc Q * P⁻¹ * (P * Q) = (Q * Q) * (P⁻¹ * P) := by ring
        _ = Q ^ 2 := by rw [inv_mul_cancel₀ hP0, mul_one, pow_two]
    rw [e1, e2] at h
    exact h
  have hPQ2 : P + Q = 2 := by
    linear_combination hsum - hP2 - hQ2
  have hsq : P ^ 2 - Q ^ 2 = P - Q := by
    rw [hP2, hQ2]
    ring
  have hdiff : (P - Q) * (P + Q - 1) = 0 := by
    linear_combination hsq
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rcases mul_eq_zero.mp hdiff with h | h
  · have hPQeq : P = Q := sub_eq_zero.mp h
    have htwoP : (2 : ZMod p) * P = 2 := by
      linear_combination hPQ2 + hPQeq
    have hPone : P = 1 := by
      apply mul_left_cancel₀ h2
      rw [htwoP, mul_one]
    rw [hPone] at hP2
    simp at hP2
  · have hPQ1 : P + Q = 1 := sub_eq_zero.mp h
    have h21 : (2 : ZMod p) = 1 := by rw [← hPQ2, hPQ1]
    have h1 : (1 : ZMod p) = 0 := by linear_combination h21
    refine h2 ?_
    calc (2 : ZMod p) = 1 + 1 := by ring
      _ = 0 + 0 := by rw [h1]
      _ = 0 := by ring

private theorem zsix_field_contra (hp : p ≠ 2) {α β xa xb xc ya yb yc : ZMod p}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hxa : xa * ya = 1) (hxb : xb * yb = 1) (hxc : xc * yc = 1)
    (h1 : (ya - α * yb) * (xa - α⁻¹ * xb) = 1)
    (h2 : (yc - β * yb) * (xc - β⁻¹ * xb) = 1)
    (h3 : (yb - α⁻¹ * ya - β⁻¹ * yc) * (xb - α * xa - β * xc) = 1) : False := by
  have hPinv : (α * xa * yb)⁻¹ = α⁻¹ * xb * ya := by
    have hxa' : xa⁻¹ = ya := inv_eq_of_mul_eq_one_right hxa
    have hyb' : yb⁻¹ = xb := inv_eq_of_mul_eq_one_left hxb
    rw [mul_inv, mul_inv, hxa', hyb']
    ring
  have hP : α * xa * yb + (α * xa * yb)⁻¹ = 1 := by
    rw [hPinv]
    have h : ya * xa - α⁻¹ * ya * xb - α * yb * xa + α * α⁻¹ * yb * xb = 1 := by
      linear_combination h1
    rw [mul_comm ya xa, hxa, mul_inv_cancel₀ hα, one_mul] at h
    rw [mul_comm yb xb, hxb] at h
    linear_combination -h
  have hQinv : (β * xc * yb)⁻¹ = β⁻¹ * xb * yc := by
    have hxc' : xc⁻¹ = yc := inv_eq_of_mul_eq_one_right hxc
    have hyb' : yb⁻¹ = xb := inv_eq_of_mul_eq_one_left hxb
    rw [mul_inv, mul_inv, hxc', hyb']
    ring
  have hQ : β * xc * yb + (β * xc * yb)⁻¹ = 1 := by
    rw [hQinv]
    have h : yc * xc - β⁻¹ * yc * xb - β * yb * xc + β * β⁻¹ * yb * xb = 1 := by
      linear_combination h2
    rw [mul_comm yc xc, hxc, mul_inv_cancel₀ hβ, one_mul] at h
    rw [mul_comm yb xb, hxb] at h
    linear_combination -h
  have hP' : α * xa * yb + α⁻¹ * xb * ya = 1 := by
    have h := hP
    rwa [hPinv] at h
  have hQ' : β * xc * yb + β⁻¹ * xb * yc = 1 := by
    have h := hQ
    rwa [hQinv] at h
  have hexp : yb * xb - α * yb * xa - β * yb * xc - α⁻¹ * ya * xb +
      α⁻¹ * α * ya * xa + α⁻¹ * β * ya * xc - β⁻¹ * yc * xb + β⁻¹ * α * yc * xa +
      β⁻¹ * β * yc * xc = 1 := by
    linear_combination h3
  rw [inv_mul_cancel₀ hα, inv_mul_cancel₀ hβ, one_mul, one_mul, mul_comm yb xb, hxb,
    mul_comm ya xa, hxa, mul_comm yc xc, hxc] at hexp
  have hcross : α⁻¹ * β * ya * xc + β⁻¹ * α * yc * xa = 0 := by
    linear_combination hexp + hP' + hQ'
  have hPQ : (α * xa * yb) * (β * xc * yb)⁻¹ + (β * xc * yb) * (α * xa * yb)⁻¹ = 0 := by
    rw [hPinv, hQinv]
    linear_combination (yb * xb) * hcross
  exact zsix_field_core hp hP hQ hPQ

private theorem zsix_pair_conj (hp : p ≠ 2) {u v us : U} {φ ψ φs : Dual (ZMod p) U}
    (h : φ u = 2) (hb : ψ v = 2) (hs : φs us = 2)
    (hs1 : orderOf (reflection hs * (reflection hb * reflection h * reflection hb)) = 3) :
    (φs u - ψ u * φs v) * (φ us - ψ us * φ v) = 1 := by
  have hb1 : (φ ∘ₗ ((reflection hb).symm : U →ₗ[ZMod p] U)) ((reflection hb) u) = 2 := by
    change φ ((reflection hb).symm ((reflection hb) u)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact h
  have hconj : reflection hb * reflection h * reflection hb = reflection hb1 := by
    simpa using conj_reflection (g := reflection hb) (u := u) (φ := φ) h hb1
  have hs1a : orderOf (reflection hs * reflection hb1) = 3 := by
    rw [hconj] at hs1
    exact hs1
  have heq := mul_eq_one_of_orderOf_eq_three hp hs hb1 hs1a
  have h1fac : φs ((reflection hb) u) = φs u - ψ u * φs v := by
    rw [Module.reflection_apply]
    simp only [map_sub, map_smul, smul_eq_mul]
  have h2fac : (φ ∘ₗ ((reflection hb).symm : U →ₗ[ZMod p] U)) us = φ us - ψ us * φ v := by
    rw [LinearMap.comp_apply]
    change φ ((reflection hb).symm us) = φ us - ψ us * φ v
    rw [Module.reflection_symm, Module.reflection_apply]
    simp only [map_sub, map_smul, smul_eq_mul]
  rw [h1fac, h2fac] at heq
  exact heq

private theorem zsix_pair_acbca (hp : p ≠ 2) {ua ub uc us : U}
    {φa φb φc φs : Dual (ZMod p) U}
    (ha : φa ua = 2) (hb : φb ub = 2) (hc : φc uc = 2) (hs : φs us = 2)
    (hac0 : φa uc = 0) (hca0 : φc ua = 0)
    (hs3 : orderOf (reflection hs * (reflection ha * reflection hc * reflection hb *
      reflection hc * reflection ha)) = 3) :
    (φs ub - φa ub * φs ua - φc ub * φs uc) *
      (φb us - φb ua * φa us - φb uc * φc us) = 1 := by
  have hginv : ((reflection ha * reflection hc) : U ≃ₗ[ZMod p] U)⁻¹
      = reflection hc * reflection ha := by
    rw [mul_inv_rev, Module.reflection_inv, Module.reflection_inv]
  have h3eq : reflection ha * reflection hc * reflection hb * reflection hc * reflection ha
      = (reflection ha * reflection hc) * reflection hb *
        (reflection ha * reflection hc)⁻¹ := by
    rw [hginv]
    simp only [mul_assoc]
  have hc3 : (φb ∘ₗ ((reflection ha * reflection hc).symm : U →ₗ[ZMod p] U))
      ((reflection ha * reflection hc) ub) = 2 := by
    change φb ((reflection ha * reflection hc).symm ((reflection ha * reflection hc) ub)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hb
  have hconj : (reflection ha * reflection hc) * reflection hb *
      (reflection ha * reflection hc)⁻¹ = reflection hc3 :=
    conj_reflection (g := reflection ha * reflection hc) (u := ub) (φ := φb) hb hc3
  have hs3a : orderOf (reflection hs * reflection hc3) = 3 := by
    rw [h3eq, hconj] at hs3
    exact hs3
  have heq := mul_eq_one_of_orderOf_eq_three hp hs hc3 hs3a
  have h1fac : φs ((reflection ha * reflection hc) ub)
      = φs ub - φa ub * φs ua - φc ub * φs uc := by
    rw [LinearEquiv.mul_apply, Module.reflection_apply, Module.reflection_apply]
    simp only [map_sub, map_smul, smul_eq_mul, hac0]
    ring
  have h2fac : (φb ∘ₗ ((reflection ha * reflection hc).symm : U →ₗ[ZMod p] U)) us
      = φb us - φb ua * φa us - φb uc * φc us := by
    rw [LinearMap.comp_apply]
    change φb ((reflection ha * reflection hc).symm us) =
      φb us - φb ua * φa us - φb uc * φc us
    have hsymm : ((reflection ha * reflection hc).symm) us
        = (reflection hc) ((reflection ha) us) := by
      rw [LinearEquiv.symm_apply_eq]
      change us = (reflection ha) ((reflection hc) ((reflection hc) ((reflection ha) us)))
      have hcc : ∀ x, (reflection hc) ((reflection hc) x) = x :=
        Module.involutive_reflection hc
      have haa : ∀ x, (reflection ha) ((reflection ha) x) = x :=
        Module.involutive_reflection ha
      rw [hcc, haa]
    rw [hsymm, Module.reflection_apply, Module.reflection_apply]
    simp only [map_sub, map_smul, smul_eq_mul, hca0]
    ring
  rw [h1fac, h2fac] at heq
  exact heq

theorem false_of_six (hp : p ≠ 2) {ua ub uc us : U} {φa φb φc φs : Dual (ZMod p) U}
    (ha : φa ua = 2) (hb : φb ub = 2) (hc : φc uc = 2) (hs : φs us = 2)
    (hac : orderOf (reflection ha * reflection hc) = 2)
    (hab : orderOf (reflection ha * reflection hb) = 3)
    (hbc : orderOf (reflection hb * reflection hc) = 3)
    (hsa : orderOf (reflection hs * reflection ha) = 3)
    (hsb : orderOf (reflection hs * reflection hb) = 3)
    (hsc : orderOf (reflection hs * reflection hc) = 3)
    (hs1 : orderOf (reflection hs * (reflection hb * reflection ha * reflection hb)) = 3)
    (hs2 : orderOf (reflection hs * (reflection hb * reflection hc * reflection hb)) = 3)
    (hs3 : orderOf (reflection hs * (reflection ha * reflection hc * reflection hb *
      reflection hc * reflection ha)) = 3) : False := by
  obtain ⟨hac0, hca0⟩ := eq_zero_of_orderOf_eq_two hp ha hc hac
  have hab1 : φa ub * φb ua = 1 := mul_eq_one_of_orderOf_eq_three hp ha hb hab
  have hbc1 : φb uc * φc ub = 1 := mul_eq_one_of_orderOf_eq_three hp hb hc hbc
  have hsa1 : φs ua * φa us = 1 := mul_eq_one_of_orderOf_eq_three hp hs ha hsa
  have hsb1 : φs ub * φb us = 1 := mul_eq_one_of_orderOf_eq_three hp hs hb hsb
  have hsc1 : φs uc * φc us = 1 := mul_eq_one_of_orderOf_eq_three hp hs hc hsc
  have hφaub : φa ub = (φb ua)⁻¹ := eq_inv_of_mul_eq_one_left hab1
  have hφcub : φc ub = (φb uc)⁻¹ := eq_inv_of_mul_eq_one_right hbc1
  have hrel1 : (φs ua - φb ua * φs ub) * (φa us - (φb ua)⁻¹ * φb us) = 1 := by
    have h := zsix_pair_conj hp ha hb hs hs1
    rw [hφaub] at h
    linear_combination h
  have hrel2 : (φs uc - φb uc * φs ub) * (φc us - (φb uc)⁻¹ * φb us) = 1 := by
    have h := zsix_pair_conj hp hc hb hs hs2
    rw [hφcub] at h
    linear_combination h
  have hrel3 : (φs ub - (φb ua)⁻¹ * φs ua - (φb uc)⁻¹ * φs uc) *
      (φb us - φb ua * φa us - φb uc * φc us) = 1 := by
    have h := zsix_pair_acbca hp ha hb hc hs hac0 hca0 hs3
    rw [hφaub, hφcub] at h
    linear_combination h
  exact zsix_field_contra hp (right_ne_zero_of_mul_eq_one hab1)
    (left_ne_zero_of_mul_eq_one hbc1)
    (by rw [mul_comm]; exact hsa1) (by rw [mul_comm]; exact hsb1)
    (by rw [mul_comm]; exact hsc1) hrel1 hrel2 hrel3

theorem false_of_six_of_isRefl [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {a b c s : U ≃ₗ[ZMod p] U} (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c)
    (hs : IsRefl p s) (hac : orderOf (a * c) = 2) (hab : orderOf (a * b) = 3)
    (hbc : orderOf (b * c) = 3) (hsa : orderOf (s * a) = 3) (hsb : orderOf (s * b) = 3)
    (hsc : orderOf (s * c) = 3) (hs1 : orderOf (s * (b * a * b)) = 3)
    (hs2 : orderOf (s * (b * c * b)) = 3) (hs3 : orderOf (s * (a * c * b * c * a)) = 3) :
    False := by
  obtain ⟨ua, φa, ha0, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨ub, φb, hb0, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨uc, φc, hc0, rfl⟩ := (isRefl_iff hp c).mp hc
  obtain ⟨us, φs, hs0, rfl⟩ := (isRefl_iff hp s).mp hs
  exact false_of_six hp ha0 hb0 hc0 hs0 hac hab hbc hsa hsb hsc hs1 hs2 hs3

end CFSG.StandardType.ZS

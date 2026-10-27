module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassCrAux
public import TauCeti.RingTheory.Henselian.BinaryForm

public section

namespace CFSG.StandardType.ZS

open Subgroup QuadraticMap

private theorem owD3_two_ne_zero_of_odd_card {K : Type*} [Field K] [Fintype K]
    (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 :=
  CFSG.RankThree.Classical.two_ne_zero_of_card_odd (by
    rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.mp hodd)

theorem owD3_binary_represents {K : Type*} [Field K] [Fintype K] (hodd : Odd (Nat.card K))
    {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hV : Module.finrank K V = 2) (t : K) (ht : t ≠ 0) :
    ∃ w : V, Q w = t := by
  have h2 : (2 : K) ≠ 0 := owD3_two_ne_zero_of_odd_card hodd
  haveI : Invertible (2 : K) := invertibleOfNonzero h2
  have hQn : Q.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff (Q := Q)).mp hQ
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; norm_num)
  obtain ⟨x, hx⟩ := hQn.exists_isUnit
  have hx0 : Q x ≠ 0 := isUnit_iff_ne_zero.mp hx
  have hxne : x ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at hx
    exact not_isUnit_zero hx
  let Vx : Submodule K V := LinearMap.BilinForm.orthogonal (polarBilin Q) (K ∙ x)
  have hVx : Module.finrank K Vx = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ (K ∙ x), finrank_span_singleton hxne, hV]
  have hVxne : Vx ≠ ⊥ := by
    intro h
    rw [h] at hVx
    simp at hVx
  obtain ⟨y, hymem, hyne⟩ := Submodule.ne_bot_iff Vx |>.mp hVxne
  let yV : Vx := ⟨y, hymem⟩
  have hyVne : yV ≠ 0 := fun h => hyne (Subtype.ext_iff.mp h)
  have hyB : polarBilin Q x y = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hymem) x (Submodule.mem_span_singleton_self x)
  have hVxnd : (polarBilin (Q.comp Vx.subtype)).Nondegenerate :=
    owCr_restrict_nondegenerate Q hQ h2 x hx0
  have hy0 : Q y ≠ 0 := by
    intro h0
    have hspan : Vx = K ∙ y :=
      eq_span_singleton_of_mem_of_finrank_eq_one hVx hymem hyne
    have hzero : ∀ z : Vx, polarBilin (Q.comp Vx.subtype) yV z = 0 := by
      intro z
      have hzmem : (z : V) ∈ K ∙ y := by rw [← hspan]; exact z.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzmem
      have hz : (z : V) = c • (y : V) := hc.symm
      have hcoe : polarBilin (Q.comp Vx.subtype) yV z = polarBilin Q (y : V) (z : V) := by
        rw [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply]
        rfl
      rw [hcoe, hz, polarBilin_apply_apply, polar_smul_right]
      have hyy : polar Q (y : V) (y : V) = 2 * Q y := by
        rw [polar_self, two_smul]
        ring
      rw [hyy, h0, mul_zero, smul_zero]
    exact hyVne (hVxnd.1 yV hzero)
  haveI : Finite (IsLocalRing.ResidueField K) :=
    Finite.of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal K)) Ideal.Quotient.mk_surjective
  obtain ⟨α, β, hαβ⟩ := TauCeti.exists_mul_sq_add_mul_sq_eq_of_isUnit (R := K)
    (isUnit_iff_ne_zero.mpr h2) (isUnit_iff_ne_zero.mpr hx0) (isUnit_iff_ne_zero.mpr hy0)
    (isUnit_iff_ne_zero.mpr ht)
  refine ⟨α • x + β • y, ?_⟩
  have hzero' : polar Q x y = 0 := by rw [← polarBilin_apply_apply]; exact hyB
  have hQx : Q (α • x) = α ^ 2 * Q x := by
    rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]
  have hQy : Q (β • y) = β ^ 2 * Q y := by
    rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]
  have hpolar : polar Q (α • x) (β • y) = 0 := by
    rw [polar_smul_left, polar_smul_right, hzero', smul_zero, smul_zero]
  rw [QuadraticMap.map_add Q, hQx, hQy, hpolar, add_zero]
  linear_combination hαβ

private theorem owD3_coeff_eq_zero {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]
    {a b : U} (hind : LinearIndependent K ![a, b]) {α β : K} (h : α • a + β • b = 0) :
    α = 0 ∧ β = 0 :=
  (LinearIndependent.pair_iff.mp hind) α β h

theorem owD3_linearIndependent_pair {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) {a b : U} {c : K} (hc : c ≠ 0)
    (ha : Q a ≠ 0) (haQ : Q a = c) (hbQ : Q b = c)
    (h4 : (polarBilin Q a b / c) ^ 2 ≠ 4) :
    LinearIndependent K ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro α β h
  by_cases hβ : β = 0
  · subst hβ
    have hzero : α • a = 0 := by simpa using h
    have hα : α = 0 := by
      rcases smul_eq_zero.mp hzero with h' | h'
      · exact h'
      · exact absurd h' (fun ha0 => ha (by rw [ha0, QuadraticMap.map_zero]))
    exact ⟨hα, rfl⟩
  · exfalso
    have h1 : β • b = -(α • a) := by
      have hcomm : β • b + α • a = 0 := by rw [add_comm]; exact h
      exact eq_neg_of_add_eq_zero_left hcomm
    have hb' : b = (-(α * β⁻¹)) • a := by
      calc b = β⁻¹ • (β • b) := (inv_smul_smul₀ hβ b).symm
        _ = β⁻¹ • (-(α • a)) := by rw [h1]
        _ = -(β⁻¹ • (α • a)) := by rw [smul_neg]
        _ = -((β⁻¹ * α) • a) := by rw [smul_smul]
        _ = (-(β⁻¹ * α)) • a := by rw [neg_smul]
        _ = (-(α * β⁻¹)) • a := by rw [mul_comm]
    have hQb : Q b = (-(α * β⁻¹)) ^ 2 * Q a := by
      rw [hb', QuadraticMap.map_smul, smul_eq_mul, pow_two]
    have hlam2 : (-(α * β⁻¹)) ^ 2 = 1 := by
      have hc' : (-(α * β⁻¹)) ^ 2 * c = c := by
        rw [← haQ, ← hQb]
        exact hbQ.trans haQ.symm
      exact mul_right_cancel₀ hc (by rw [hc', one_mul])
    have hBab : polarBilin Q a b = (-(α * β⁻¹)) * (2 * c) := by
      rw [hb', polarBilin_apply_apply, polar_smul_right, polar_self, haQ]
      ring
    have hx2 : (polarBilin Q a b / c) ^ 2 = 4 := by
      have hdiv : polarBilin Q a b / c = 2 * (-(α * β⁻¹)) := by
        rw [hBab, show (-(α * β⁻¹)) * (2 * c) = ((-(α * β⁻¹)) * 2) * c by ring,
          mul_div_cancel_right₀ _ hc]
        ring
      rw [hdiv, mul_pow, hlam2]
      norm_num
    exact h4 hx2

theorem owD3_order_criterion {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]
    [Finite U] (h2 : (2 : K) ≠ 0)
    (Q : QuadraticForm K U) {a b : U} {c x : K} (hc : c ≠ 0)
    (ha : Q a ≠ 0) (hb : Q b ≠ 0) (haQ : Q a = c) (hbQ : Q b = c)
    (hx : polarBilin Q a b / c = x)
    (hx0 : x ≠ 0) (hx1 : x ^ 2 ≠ 1) (hx2 : x ^ 2 ≠ 2) (hx4 : x ^ 2 ≠ 4) :
    4 < orderOf (owCr_orthRefl Q a ha * owCr_orthRefl Q b hb) := by
  haveI : Finite (U ≃ₗ[K] U) :=
    Finite.of_injective (fun e : U ≃ₗ[K] U => (e : U → U))
      (fun e₁ e₂ h => LinearEquiv.ext (fun v => congrFun h v))
  let ra : U ≃ₗ[K] U := owCr_orthRefl Q a ha
  let rb : U ≃ₗ[K] U := owCr_orthRefl Q b hb
  let T : U ≃ₗ[K] U := ra * rb
  have hind : LinearIndependent K ![a, b] :=
    owD3_linearIndependent_pair Q hc ha haQ hbQ (by rw [hx]; exact hx4)
  have hBba : polarBilin Q b a = polarBilin Q a b := by
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]
  have hra : ra a = -a := owCr_orthRefl_self Q a ha
  have hrb_b : rb b = -b := owCr_orthRefl_self Q b hb
  have hrb_a : rb a = a - x • b := by
    change owCr_orthRefl Q b hb a = a - x • b
    rw [owCr_orthRefl_apply, hbQ, hx]
  have hra_b : ra b = b - x • a := by
    change owCr_orthRefl Q a ha b = b - x • a
    rw [owCr_orthRefl_apply, haQ, hBba, hx]
  have hTa : T a = (x ^ 2 - 1) • a - x • b := by
    change ra (rb a) = (x ^ 2 - 1) • a - x • b
    rw [hrb_a, map_sub, map_smul, hra, hra_b]
    module
  have hTb : T b = x • a - b := by
    change ra (rb b) = x • a - b
    rw [hrb_b, map_neg, hra_b]
    module
  have hT2a : (T ^ 2) a = (x ^ 2 - 2) • T a - a := by
    calc (T ^ 2) a = T (T a) := by rw [pow_two, LinearEquiv.mul_apply]
      _ = T ((x ^ 2 - 1) • a - x • b) := by rw [hTa]
      _ = T ((x ^ 2 - 1) • a) - T (x • b) := by rw [map_sub]
      _ = (x ^ 2 - 1) • T a - x • T b := by rw [LinearEquiv.map_smul, LinearEquiv.map_smul]
      _ = (x ^ 2 - 1) • ((x ^ 2 - 1) • a - x • b) - x • (x • a - b) := by rw [hTa, hTb]
      _ = (x ^ 2 - 2) • T a - a := by rw [hTa]; module
  have hT3a : (T ^ 3) a = ((x ^ 2 - 2) ^ 2 - 1) • T a - (x ^ 2 - 2) • a := by
    calc (T ^ 3) a = T ((T ^ 2) a) := by rw [pow_succ', LinearEquiv.mul_apply]
      _ = T ((x ^ 2 - 2) • T a - a) := by rw [hT2a]
      _ = T ((x ^ 2 - 2) • T a) - T a := by rw [map_sub]
      _ = (x ^ 2 - 2) • T (T a) - T a := by rw [LinearEquiv.map_smul]
      _ = (x ^ 2 - 2) • ((T ^ 2) a) - T a := by rw [show T (T a) = (T ^ 2) a by rfl]
      _ = (x ^ 2 - 2) • ((x ^ 2 - 2) • T a - a) - T a := by rw [hT2a]
      _ = ((x ^ 2 - 2) ^ 2 - 1) • T a - (x ^ 2 - 2) • a := by module
  have hT4a : (T ^ 4) a
      = ((x ^ 2 - 2) * ((x ^ 2 - 2) ^ 2 - 2)) • T a + (1 - (x ^ 2 - 2) ^ 2) • a := by
    calc (T ^ 4) a = T ((T ^ 3) a) := by rw [pow_succ', LinearEquiv.mul_apply]
      _ = T (((x ^ 2 - 2) ^ 2 - 1) • T a - (x ^ 2 - 2) • a) := by rw [hT3a]
      _ = T (((x ^ 2 - 2) ^ 2 - 1) • T a) - T ((x ^ 2 - 2) • a) := by rw [map_sub]
      _ = ((x ^ 2 - 2) ^ 2 - 1) • T (T a) - (x ^ 2 - 2) • T a := by rw [LinearEquiv.map_smul, LinearEquiv.map_smul]
      _ = ((x ^ 2 - 2) ^ 2 - 1) • ((T ^ 2) a) - (x ^ 2 - 2) • T a := by rw [show T (T a) = (T ^ 2) a by rfl]
      _ = ((x ^ 2 - 2) ^ 2 - 1) • ((x ^ 2 - 2) • T a - a) - (x ^ 2 - 2) • T a := by rw [hT2a]
      _ = ((x ^ 2 - 2) * ((x ^ 2 - 2) ^ 2 - 2)) • T a + (1 - (x ^ 2 - 2) ^ 2) • a := by module
  have hTpow_ne : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → T ^ k ≠ 1 := by
    intro k hk1 hk4
    have hka_ne : (T ^ k) a ≠ a := by
      intro hka
      interval_cases k
      · have hka' : T a = a := by simpa using hka
        have hh : (x ^ 2 - 2) • a + (-x) • b = 0 := by
          have h1 : (x ^ 2 - 2) • a + (-x) • b = T a - a := by
            rw [hTa]; module
          rw [h1, hka', sub_self]
        have hcoef := owD3_coeff_eq_zero hind hh
        exact hx0 (by simpa using hcoef.2)
      · have hka' : (T ^ 2) a = a := hka
        have hh : ((x ^ 2 - 2) * (x ^ 2 - 1) - 2) • a + (-((x ^ 2 - 2) * x)) • b = 0 := by
          have h1 : ((x ^ 2 - 2) * (x ^ 2 - 1) - 2) • a + (-((x ^ 2 - 2) * x)) • b
              = (x ^ 2 - 2) • T a - 2 • a := by
            rw [hTa]; module
          have h2' : (x ^ 2 - 2) • T a - 2 • a = (T ^ 2) a - a := by
            rw [hT2a]; module
          rw [h1, h2', hka', sub_self]
        have hcoef := owD3_coeff_eq_zero hind hh
        have hs0 : x ^ 2 - 2 = 0 := by
          have hb := hcoef.2
          rw [neg_eq_zero] at hb
          rcases mul_eq_zero.mp hb with h | h
          · exact h
          · exact absurd h hx0
        have h2zero : (2 : K) = 0 := by
          have ha' := hcoef.1
          rw [hs0] at ha'
          have hneg : -(2 : K) = 0 := by simpa using ha'
          exact neg_eq_zero.mp hneg
        exact h2 h2zero
      · have hka' : (T ^ 3) a = a := hka
        have hh : (((x ^ 2 - 2) ^ 2 - 1) * (x ^ 2 - 1) - (x ^ 2 - 2) - 1) • a
            + (-(((x ^ 2 - 2) ^ 2 - 1) * x)) • b = 0 := by
          have h1 : (((x ^ 2 - 2) ^ 2 - 1) * (x ^ 2 - 1) - (x ^ 2 - 2) - 1) • a
              + (-(((x ^ 2 - 2) ^ 2 - 1) * x)) • b
              = ((x ^ 2 - 2) ^ 2 - 1) • T a - (x ^ 2 - 2) • a - a := by
            rw [hTa]; module
          have h2' : ((x ^ 2 - 2) ^ 2 - 1) • T a - (x ^ 2 - 2) • a - a = (T ^ 3) a - a := by
            rw [hT3a]
          rw [h1, h2', hka', sub_self]
        have hcoef := owD3_coeff_eq_zero hind hh
        have hs2 : (x ^ 2 - 2) ^ 2 = 1 := by
          have hb := hcoef.2
          rw [neg_eq_zero] at hb
          rcases mul_eq_zero.mp hb with h | h
          · linear_combination h
          · exact absurd h hx0
        have hsneg : x ^ 2 - 2 = -1 := by
          have ha' := hcoef.1
          rw [hs2] at ha'
          have hsum : (x ^ 2 - 2) + 1 = 0 := by linear_combination -ha'
          exact eq_neg_of_add_eq_zero_left hsum
        exact hx1 (by linear_combination hsneg)
      · have hka' : (T ^ 4) a = a := hka
        have hh : ((x ^ 2 - 2) * ((x ^ 2 - 2) ^ 2 - 2) * (x ^ 2 - 1) + (1 - (x ^ 2 - 2) ^ 2) - 1) • a
            + (-((x ^ 2 - 2) * ((x ^ 2 - 2) ^ 2 - 2) * x)) • b = 0 := by
          have h1 : ((x ^ 2 - 2) * ((x ^ 2 - 2) ^ 2 - 2) * (x ^ 2 - 1)
                + (1 - (x ^ 2 - 2) ^ 2) - 1) • a
              + (-((x ^ 2 - 2) * ((x ^ 2 - 2) ^ 2 - 2) * x)) • b
              = ((x ^ 2 - 2) * ((x ^ 2 - 2) ^ 2 - 2)) • T a + (1 - (x ^ 2 - 2) ^ 2) • a - a := by
            rw [hTa]; module
          have h2' : ((x ^ 2 - 2) * ((x ^ 2 - 2) ^ 2 - 2)) • T a + (1 - (x ^ 2 - 2) ^ 2) • a - a
              = (T ^ 4) a - a := by
            rw [hT4a]
          rw [h1, h2', hka', sub_self]
        have hcoef := owD3_coeff_eq_zero hind hh
        have hb := hcoef.2
        rw [neg_eq_zero] at hb
        rcases mul_eq_zero.mp hb with h' | hxzero
        · rcases mul_eq_zero.mp h' with hs0 | hs22
          · exact hx2 (by linear_combination hs0)
          · have hs22' : (x ^ 2 - 2) ^ 2 = 2 := by linear_combination hs22
            have ha' := hcoef.1
            rw [hs22, hs22'] at ha'
            have hneg2 : -(2 : K) = 0 := by simpa using ha'
            exact h2 (neg_eq_zero.mp hneg2)
        · exact absurd hxzero hx0
    intro hk
    exact hka_ne (by rw [hk]; rfl)
  change 4 < orderOf T
  have hfin : IsOfFinOrder T := isOfFinOrder_of_finite T
  have hpos : 0 < orderOf T := orderOf_pos_iff.mpr hfin
  by_contra hcon
  push Not at hcon
  have hcases : orderOf T = 1 ∨ orderOf T = 2 ∨ orderOf T = 3 ∨ orderOf T = 4 := by omega
  rcases hcases with h | h | h | h
  · exact hTpow_ne 1 le_rfl (by norm_num) (by simpa [h] using pow_orderOf_eq_one T)
  · exact hTpow_ne 2 (by norm_num) (by norm_num) (by simpa [h] using pow_orderOf_eq_one T)
  · exact hTpow_ne 3 (by norm_num) (by norm_num) (by simpa [h] using pow_orderOf_eq_one T)
  · exact hTpow_ne 4 (by norm_num) (by norm_num) (by simpa [h] using pow_orderOf_eq_one T)

end CFSG.StandardType.ZS

end

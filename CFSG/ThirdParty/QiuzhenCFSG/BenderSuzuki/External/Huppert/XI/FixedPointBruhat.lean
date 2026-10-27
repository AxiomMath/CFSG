module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.GeneralRhoBruhat

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki.External

private theorem xi1115_fixed_point_alpha_coordinate
    {K F D : Type*} [Field K] [CharP K 2]
    [Group F] [Group D] [MulDistribMulAction D F]
    (theta : K ≃+* K) (pair : K → K → F) (eD : D ≃* Kˣ)
    (hone : pair 0 0 = 1)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w = pair (a + b) (z + w + a * theta b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z = pair ((eD d : K) * a)
        ((eD d : K) * theta (eD d : K) * z))
    (j g : F) (rho : K) (hj : j = pair 0 1) (hg : g = pair 1 rho)
    (hjne : j ≠ 1) (hgne : g ≠ 1)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hJCoord : coord ⟨j, hjne⟩ = (g, 1, g⁻¹))
    (hGCoord : coord ⟨g, hgne⟩ = (j, 1, g))
    (hGInvCoord : coord ⟨g⁻¹, inv_ne_one.mpr hgne⟩ = (g⁻¹, 1, j))
    (hcoordCov : ∀ (d : D) (x : {x : F // x ≠ 1}),
      let dx : {x : F // x ≠ 1} := ⟨d • x.1, by
        intro h
        apply x.2
        calc
          x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
          _ = d⁻¹ • 1 := by rw [h]
          _ = 1 := smul_one _⟩
      coord dx =
        (d⁻¹ • (coord x).1,
          d⁻¹ * d⁻¹ * (coord x).2.1,
          d⁻¹ • (coord x).2.2))
    (hproductAlpha :
      ∀ (x₁ x₂ : {x : F // x ≠ 1})
        (hprod : x₁.1 * x₂.1 ≠ 1)
        (hmiddle : (coord x₁).2.2 * (coord x₂).1 ≠ 1),
        let x₁₂ : {x : F // x ≠ 1} := ⟨x₁.1 * x₂.1, hprod⟩
        let middle : {x : F // x ≠ 1} :=
          ⟨(coord x₁).2.2 * (coord x₂).1, hmiddle⟩
        (coord x₁₂).2.2 =
          (coord x₂).2.1 • (coord middle).2.2 * (coord x₂).2.2)
    (u : K) (huFix : theta u = u) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    let xu : {x : F // x ≠ 1} :=
      ⟨pair 1 (rho + u), by
        intro h
        have hc := hinj 1 (rho + u) 0 0 (h.trans hone.symm)
        exact one_ne_zero hc.1⟩
    (coord xu).2.2 = pair 1 (rho + u * (1 + u)⁻¹) := by
  dsimp only
  have huOneAdd : 1 + u ≠ 0 := by
    intro h
    apply hu1
    exact ((eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq _)).symm
  let ell : K := (u * (1 + u))⁻¹
  have hell : ell ≠ 0 := inv_ne_zero (mul_ne_zero hu0 huOneAdd)
  have hthetaOneAdd : theta (1 + u) = 1 + u := by
    simp only [map_add, map_one, huFix]
  have hfactorSecond :
      (1 * u) * theta (1 * u) * (rho + 1) +
          (1 * (1 + u)) * theta (1 * (1 + u)) * rho +
            (1 * u) * theta (1 * (1 + u)) = rho + u := by
    simp only [one_mul, huFix, hthetaOneAdd]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  have hellNorm :
      ell * theta ell =
        ((1 * u)⁻¹ * theta (1 * u)⁻¹) +
          ((1 * (1 + u))⁻¹ * theta (1 * (1 + u))⁻¹) := by
    dsimp only [ell]
    simp only [one_mul, map_inv₀, map_mul, huFix, hthetaOneAdd]
    field_simp [hu0, huOneAdd]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  have htargetNe : pair 1 (rho + u) ≠ 1 := by
    intro h
    have hc := hinj 1 (rho + u) 0 0 (h.trans hone.symm)
    exact one_ne_zero hc.1
  have hgeneral :=
    xi1115_alpha_coordinate_of_inverse_structure_factorization_nondegenerate
        theta pair eD hone hinj hmul hactor j g rho hj hg hjne hgne coord
        hJCoord hGCoord hGInvCoord hcoordCov hproductAlpha
        1 (rho + u) u ell one_ne_zero hu0 hu1 hell hfactorSecond hellNorm
        htargetNe
  dsimp only at hgeneral
  rw [hgeneral]
  apply congrArg₂ pair
  · dsimp only [ell]
    field_simp [hu0, huOneAdd]
    ring_nf
  · dsimp only [ell]
    simp only [map_mul, map_add, map_one, map_inv₀, map_pow, huFix]
    field_simp [hu0, huOneAdd]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

set_option maxHeartbeats 800000 in
public theorem xi1115_theta_fixed_points_of_bruhat_product
    {K F D : Type*} [Field K] [CharP K 2]
    [Group F] [Group D] [MulDistribMulAction D F]
    (theta : K ≃+* K) (pair : K → K → F) (eD : D ≃* Kˣ)
    (hone : pair 0 0 = 1)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w = pair (a + b) (z + w + a * theta b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z = pair ((eD d : K) * a)
        ((eD d : K) * theta (eD d : K) * z))
    (j g : F) (rho : K) (hj : j = pair 0 1) (hg : g = pair 1 rho)
    (hjne : j ≠ 1) (hgne : g ≠ 1)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hJCoord : coord ⟨j, hjne⟩ = (g, 1, g⁻¹))
    (hGCoord : coord ⟨g, hgne⟩ = (j, 1, g))
    (hGInvCoord : coord ⟨g⁻¹, inv_ne_one.mpr hgne⟩ = (g⁻¹, 1, j))
    (hcoordCov : ∀ (d : D) (x : {x : F // x ≠ 1}),
      let dx : {x : F // x ≠ 1} := ⟨d • x.1, by
        intro h
        apply x.2
        calc
          x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
          _ = d⁻¹ • 1 := by rw [h]
          _ = 1 := smul_one _⟩
      coord dx =
        (d⁻¹ • (coord x).1,
          d⁻¹ * d⁻¹ * (coord x).2.1,
          d⁻¹ • (coord x).2.2))
    (hproductAlpha :
      ∀ (x₁ x₂ : {x : F // x ≠ 1})
        (hprod : x₁.1 * x₂.1 ≠ 1)
        (hmiddle : (coord x₁).2.2 * (coord x₂).1 ≠ 1),
        let x₁₂ : {x : F // x ≠ 1} := ⟨x₁.1 * x₂.1, hprod⟩
        let middle : {x : F // x ≠ 1} :=
          ⟨(coord x₁).2.2 * (coord x₂).1, hmiddle⟩
        (coord x₁₂).2.2 =
          (coord x₂).2.1 • (coord middle).2.2 * (coord x₂).2.2) :
    ∀ u : K, theta u = u → u = 0 ∨ u = 1 := by
  intro u huFix
  by_cases hu0 : u = 0
  · exact Or.inl hu0
  right
  by_contra hu1
  have square_eq_one {x : K} (hx : x ^ 2 = 1) : x = 1 := by
    have hsq : (x + 1) ^ 2 = 0 := by
      ring_nf
      simp only [hx, CharTwo.two_eq_zero, mul_zero, add_zero,
        CharTwo.add_self_eq_zero]
    have hzero : x + 1 = 0 := sq_eq_zero_iff.mp hsq
    apply add_right_cancel (b := (1 : K))
    rw [hzero, CharTwo.add_self_eq_zero]
  have huSq0 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
  have huSq1 : u ^ 2 ≠ 1 := by
    intro h
    exact hu1 (square_eq_one h)
  let a : K := 1 + u ^ 2
  have ha0 : a ≠ 0 := by
    intro h
    apply huSq1
    exact ((eq_neg_of_add_eq_zero_left h).trans
      (CharTwo.neg_eq (u ^ 2))).symm
  have ha1 : a ≠ 1 := by
    intro h
    apply huSq0
    apply add_left_cancel (a := (1 : K))
    simpa [a] using h
  have haFix : theta a = a := by
    simp only [a, map_add, map_one, map_pow, huFix]
  let q : K := u⁻¹ ^ 2
  have hq0 : q ≠ 0 := pow_ne_zero 2 (inv_ne_zero hu0)
  have hq1 : q ≠ 1 := by
    intro h
    apply hu1
    have huInv : u⁻¹ = 1 := square_eq_one (by simpa [q] using h)
    exact inv_eq_one.mp huInv
  have hqFix : theta q = q := by
    simp only [q, map_pow, map_inv₀, huFix]
  have pairFirstNe (z : K) : pair 1 z ≠ 1 := by
    intro h
    have hc := hinj 1 z 0 0 (h.trans hone.symm)
    exact one_ne_zero hc.1
  have pairCentralNe (z : K) (hz : z ≠ 0) : pair 0 z ≠ 1 := by
    intro h
    have hc := hinj 0 z 0 0 (h.trans hone.symm)
    exact hz hc.2
  have hginv : g⁻¹ = pair 1 (rho + 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hg, hmul]
    calc
      pair (1 + 1) (rho + (rho + 1) + 1 * theta 1) = pair 0 0 := by
        apply congrArg₂ pair
        · exact CharTwo.add_self_eq_zero 1
        · rw [map_one]
          ring_nf
          simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
      _ = 1 := hone
  let xA : {x : F // x ≠ 1} :=
    ⟨pair 1 (rho + a), pairFirstNe (rho + a)⟩
  let xG : {x : F // x ≠ 1} := ⟨g, hgne⟩
  let xC : {x : F // x ≠ 1} :=
    ⟨pair 0 (u ^ 2), pairCentralNe (u ^ 2) huSq0⟩
  let xQ : {x : F // x ≠ 1} :=
    ⟨pair 1 (rho + q), pairFirstNe (rho + q)⟩
  have hAlphaA := xi1115_fixed_point_alpha_coordinate theta pair eD hone hinj
    hmul hactor j g rho hj hg hjne hgne coord hJCoord hGCoord hGInvCoord
    hcoordCov hproductAlpha a haFix ha0 ha1
  have hAlphaQ := xi1115_fixed_point_alpha_coordinate theta pair eD hone hinj
    hmul hactor j g rho hj hg hjne hgne coord hJCoord hGCoord hGInvCoord
    hcoordCov hproductAlpha q hqFix hq0 hq1
  have hAlphaA' : (coord xA).2.2 = pair 1 (rho + 1 + q) := by
    dsimp only at hAlphaA
    rw [hAlphaA]
    apply congrArg₂ pair rfl
    rw [add_assoc]
    apply add_left_cancel (a := rho)
    dsimp only [a, q]
    field_simp [hu0, huSq0]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]
    field_simp [huSq0]
  have hAlphaQ' : (coord xQ).2.2 =
      pair 1 (rho + q * (1 + q)⁻¹) := by
    simpa only [xQ] using hAlphaQ
  have hprodValue : xA.1 * xG.1 = xC.1 := by
    dsimp only [xA, xG, xC]
    rw [hg, hmul]
    apply congrArg₂ pair
    · exact CharTwo.add_self_eq_zero 1
    · dsimp only [a]
      rw [map_one]
      ring_nf
      simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]
  have hprodNe : xA.1 * xG.1 ≠ 1 := by
    rw [hprodValue]
    exact xC.2
  have hmiddleValue : (coord xA).2.2 * (coord xG).1 = xQ.1 := by
    rw [hAlphaA', hGCoord]
    dsimp only [xQ]
    rw [hj, hmul]
    apply congrArg₂ pair
    · simp only [add_zero]
    · rw [map_zero]
      ring_nf
      simp only [CharTwo.two_eq_zero, zero_add]
  have hmiddleNe : (coord xA).2.2 * (coord xG).1 ≠ 1 := by
    rw [hmiddleValue]
    exact xQ.2
  have hproduct := hproductAlpha xA xG hprodNe hmiddleNe
  let xprod : {x : F // x ≠ 1} := ⟨xA.1 * xG.1, hprodNe⟩
  let xmiddle : {x : F // x ≠ 1} :=
    ⟨(coord xA).2.2 * (coord xG).1, hmiddleNe⟩
  have hxprod : xprod = xC := Subtype.ext hprodValue
  have hxmiddle : xmiddle = xQ := Subtype.ext hmiddleValue
  change (coord xprod).2.2 =
    (coord xG).2.1 • (coord xmiddle).2.2 * (coord xG).2.2 at hproduct
  rw [hxprod, hxmiddle, hGCoord, hAlphaQ'] at hproduct
  simp only [one_smul] at hproduct
  let d : D := eD.symm (Units.mk0 u hu0)
  have heDd : (eD d : K) = u := by simp [d]
  have heDdInv : (eD d⁻¹ : K) = u⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, heDd]
  let xJ : {x : F // x ≠ 1} := ⟨j, hjne⟩
  let dxJ : {x : F // x ≠ 1} := ⟨d • xJ.1, by
    intro h
    apply xJ.2
    calc
      xJ.1 = d⁻¹ • (d • xJ.1) := (inv_smul_smul d xJ.1).symm
      _ = d⁻¹ • 1 := by rw [h]
      _ = 1 := smul_one _⟩
  have hdxJ : dxJ = xC := by
    apply Subtype.ext
    dsimp only [dxJ, xJ, xC]
    rw [hj, hactor, heDd, huFix]
    simp only [mul_zero, mul_one, pow_two]
  have hcovJ := hcoordCov d xJ
  change coord dxJ =
    (d⁻¹ • (coord xJ).1,
      d⁻¹ * d⁻¹ * (coord xJ).2.1,
      d⁻¹ • (coord xJ).2.2) at hcovJ
  rw [hdxJ, hJCoord] at hcovJ
  have hAlphaC : (coord xC).2.2 = pair u⁻¹
      (u⁻¹ * theta u⁻¹ * (rho + 1)) := by
    have h := congrArg (fun p : F × D × F => p.2.2) hcovJ
    dsimp only at h
    rw [hginv, hactor, heDdInv] at h
    simpa only [mul_one] using h
  rw [hAlphaC, hg, hmul] at hproduct
  have hfirst := (hinj _ _ _ _ hproduct).1
  simp only [CharTwo.add_self_eq_zero] at hfirst
  exact (inv_ne_zero hu0) hfirst

end CFSG.BenderSuzuki.External

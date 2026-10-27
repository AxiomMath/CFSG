module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki.External

public theorem xi1115_alpha_coordinate_of_inverse_structure_factorization_nondegenerate
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
    (c z t ell : K) (hc : c ≠ 0) (ht : t ≠ 0) (htOne : t ≠ 1)
    (hell : ell ≠ 0)
    (hfactorSecond :
      (c * t) * theta (c * t) * (rho + 1) +
          (c * (1 + t)) * theta (c * (1 + t)) * rho +
            (c * t) * theta (c * (1 + t)) = z)
    (hellNorm :
      ell * theta ell =
        ((c * t)⁻¹ * theta (c * t)⁻¹) +
          ((c * (1 + t))⁻¹ * theta (c * (1 + t))⁻¹))
    (hcz : pair c z ≠ 1) :
    let b := c * (1 + t)
    let u := b⁻¹ ^ 2 * ell⁻¹
    (coord ⟨pair c z, hcz⟩).2.2 =
      pair (u + b⁻¹)
        (u * theta u * (rho + 1) +
          b⁻¹ * theta b⁻¹ * rho + u * theta b⁻¹) := by
  dsimp only
  let a : K := c * t
  let b : K := c * (1 + t)
  let I : K → F := fun q => pair q (q * theta q * (rho + 1))
  let G : K → F := fun q => pair q (q * theta q * rho)
  let u : K := b⁻¹ ^ 2 * ell⁻¹
  have htAdd : 1 + t ≠ 0 := by
    intro h
    apply htOne
    exact ((eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq t)).symm
  have ha : a ≠ 0 := mul_ne_zero hc ht
  have hb : b ≠ 0 := mul_ne_zero hc htAdd
  have hthetaEll : theta ell ≠ 0 := (map_ne_zero theta).mpr hell
  have hpairNeOneOfFirst (A Z : K) (hA : A ≠ 0) : pair A Z ≠ 1 := by
    intro h
    have hcoords := hinj A Z 0 0 (h.trans hone.symm)
    exact hA hcoords.1
  have hpairNeOneOfSecond (Z : K) (hZ : Z ≠ 0) : pair 0 Z ≠ 1 := by
    intro h
    have hcoords := hinj 0 Z 0 0 (h.trans hone.symm)
    exact hZ hcoords.2
  have hginv : g⁻¹ = pair 1 (rho + 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hg, hmul]
    ring_nf
    simp only [CharTwo.two_eq_zero, CharTwo.add_self_eq_zero, mul_zero,
      add_zero, map_one]
    exact hone
  let act (d : D) (x : {x : F // x ≠ 1}) : {x : F // x ≠ 1} :=
    ⟨d • x.1, by
      intro h
      apply x.2
      calc
        x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
        _ = d⁻¹ • 1 := by rw [h]
        _ = 1 := smul_one _⟩
  have hcov (d : D) (x : {x : F // x ≠ 1}) :
      coord (act d x) =
        (d⁻¹ • (coord x).1,
          d⁻¹ * d⁻¹ * (coord x).2.1,
          d⁻¹ • (coord x).2.2) := by
    simpa only [act] using hcoordCov d x
  have hfactor : pair c z = I a * G b := by
    dsimp only [I, G]
    rw [hmul]
    apply congrArg₂ pair
    · dsimp only [a, b]
      ring_nf
      simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
    · simpa only [a, b] using hfactorSecond.symm
  have hIne : I a ≠ 1 :=
    hpairNeOneOfFirst a (a * theta a * (rho + 1)) ha
  have hGne : G b ≠ 1 := hpairNeOneOfFirst b (b * theta b * rho) hb
  let xI : {x : F // x ≠ 1} := ⟨I a, hIne⟩
  let xG : {x : F // x ≠ 1} := ⟨G b, hGne⟩
  let xJ : {x : F // x ≠ 1} := ⟨j, hjne⟩
  let xg : {x : F // x ≠ 1} := ⟨g, hgne⟩
  let xgi : {x : F // x ≠ 1} := ⟨g⁻¹, inv_ne_one.mpr hgne⟩
  let da : D := eD.symm (Units.mk0 a ha)
  let db : D := eD.symm (Units.mk0 b hb)
  let de : D := eD.symm (Units.mk0 ell hell)
  have heDa : (eD da : K) = a := by simp [da]
  have heDb : (eD db : K) = b := by simp [db]
  have heDe : (eD de : K) = ell := by simp [de]
  have heDaInv : (eD da⁻¹ : K) = a⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, heDa]
  have heDbInv : (eD db⁻¹ : K) = b⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, heDb]
  have heDeInv : (eD de⁻¹ : K) = ell⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, heDe]
  have hIorbit : act da xgi = xI := by
    apply Subtype.ext
    dsimp only [act, xgi, xI, I]
    rw [hginv, hactor, heDa]
    simp only [mul_one]
  have hGorbit : act db xg = xG := by
    apply Subtype.ext
    dsimp only [act, xg, xG, G]
    rw [hg, hactor, heDb]
    simp only [mul_one]
  have hcoordI := hcov da xgi
  have hcoordG := hcov db xg
  rw [hIorbit] at hcoordI
  rw [hGorbit] at hcoordG
  change coord xgi = (g⁻¹, 1, j) at hGInvCoord
  change coord xg = (j, 1, g) at hGCoord
  rw [hGInvCoord] at hcoordI
  rw [hGCoord] at hcoordG
  have halphaI : (coord xI).2.2 = pair 0 (a⁻¹ * theta a⁻¹) := by
    have h := congrArg (fun p : F × D × F => p.2.2) hcoordI
    dsimp only at h
    rw [hj, hactor, heDaInv] at h
    simpa only [mul_zero, mul_one] using h
  have hbetaG : (coord xG).1 = pair 0 (b⁻¹ * theta b⁻¹) := by
    have h := congrArg (fun p : F × D × F => p.1) hcoordG
    dsimp only at h
    rw [hj, hactor, heDbInv] at h
    simpa only [mul_zero, mul_one] using h
  have hgammaG : (coord xG).2.1 = db⁻¹ * db⁻¹ := by
    have h := congrArg (fun p : F × D × F => p.2.1) hcoordG
    simpa only [mul_one] using h
  have halphaG : (coord xG).2.2 = G b⁻¹ := by
    have h := congrArg (fun p : F × D × F => p.2.2) hcoordG
    dsimp only [G] at h ⊢
    rw [hg, hactor, heDbInv] at h
    simpa only [mul_one] using h
  have hmiddleValue :
      (coord xI).2.2 * (coord xG).1 = pair 0 (ell * theta ell) := by
    rw [halphaI, hbetaG, hmul]
    apply congrArg₂ pair
    · simp only [zero_add]
    · simp only [zero_mul, add_zero]
      simpa only [a, b] using hellNorm.symm
  have hmiddleNe : (coord xI).2.2 * (coord xG).1 ≠ 1 := by
    rw [hmiddleValue]
    exact hpairNeOneOfSecond (ell * theta ell)
      (mul_ne_zero hell hthetaEll)
  let xmiddle : {x : F // x ≠ 1} :=
    ⟨(coord xI).2.2 * (coord xG).1, hmiddleNe⟩
  have hmiddleOrbit : act de xJ = xmiddle := by
    apply Subtype.ext
    dsimp only [act, xJ, xmiddle]
    rw [hmiddleValue, hj, hactor, heDe]
    simp only [mul_zero, mul_one]
  have hcoordMiddle := hcov de xJ
  rw [hmiddleOrbit] at hcoordMiddle
  change coord xJ = (g, 1, g⁻¹) at hJCoord
  rw [hJCoord] at hcoordMiddle
  have halphaMiddle : (coord xmiddle).2.2 = I ell⁻¹ := by
    have h := congrArg (fun p : F × D × F => p.2.2) hcoordMiddle
    dsimp only [I] at h ⊢
    rw [hginv, hactor, heDeInv] at h
    simpa only [mul_one] using h
  have hprodNe : (xI.1 * xG.1) ≠ 1 := by
    change I a * G b ≠ 1
    rw [← hfactor]
    exact hcz
  let xprod : {x : F // x ≠ 1} := ⟨xI.1 * xG.1, hprodNe⟩
  let xcz : {x : F // x ≠ 1} := ⟨pair c z, hcz⟩
  have hxprod : xprod = xcz := by
    apply Subtype.ext
    exact hfactor.symm
  have hproduct := hproductAlpha xI xG hprodNe hmiddleNe
  change (coord xprod).2.2 =
    (coord xG).2.1 • (coord xmiddle).2.2 * (coord xG).2.2 at hproduct
  rw [hxprod, halphaMiddle, halphaG] at hproduct
  have heGamma : (eD ((coord xG).2.1) : K) = b⁻¹ ^ 2 := by
    rw [hgammaG]
    simp only [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val,
      heDb, pow_two]
  have hgammaAction : (coord xG).2.1 • I ell⁻¹ = I u := by
    dsimp only [I]
    rw [hactor, heGamma]
    apply congrArg₂ pair
    · rfl
    · dsimp only [u]
      simp only [map_mul]
      ring
  rw [hgammaAction] at hproduct
  calc
    (coord ⟨pair c z, hcz⟩).2.2 = (coord xcz).2.2 := rfl
    _ = I u * G b⁻¹ := hproduct
    _ = pair (u + b⁻¹)
        (u * theta u * (rho + 1) +
          b⁻¹ * theta b⁻¹ * rho + u * theta b⁻¹) := by
      dsimp only [I, G]
      rw [hmul]
    _ = pair (b⁻¹ ^ 2 * ell⁻¹ + b⁻¹)
        ((b⁻¹ ^ 2 * ell⁻¹) * theta (b⁻¹ ^ 2 * ell⁻¹) * (rho + 1) +
          b⁻¹ * theta b⁻¹ * rho +
            (b⁻¹ ^ 2 * ell⁻¹) * theta b⁻¹) := by rfl

end CFSG.BenderSuzuki.External

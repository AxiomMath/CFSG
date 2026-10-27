module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki.External
namespace XI1115ThetaEquationExtraction

set_option maxHeartbeats 800000 in
/-- Field-algebra translation of XI.11.13(b) from Huppert's coordinates to
the aligned Type-A coordinates used in `theorem_11_15`. -/
public theorem aligned_generic_coordinate_core
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K)
    (a z sigma lambda nu : K)
    (ha : a ≠ 0) (hsigma : sigma ≠ 0)
    (hlambda : lambda ≠ 0) (hnu : nu ≠ 0)
    (hb : z + a * theta a ≠ 0)
    (hsigmaFirst : sigma * a = 1 + lambda)
    (hsigmaSecond :
      sigma * theta sigma * z = (1 + lambda) * theta lambda) :
    let epsilon : K :=
      (1 + lambda) * (lambda⁻¹ + nu⁻¹)
    theta lambda = z * (z + a * theta a)⁻¹ ∧
      sigma * (lambda⁻¹ + nu⁻¹) = epsilon * a⁻¹ ∧
      sigma * theta sigma *
          (lambda⁻¹ * theta lambda⁻¹ +
            nu⁻¹ * theta lambda⁻¹) =
        epsilon * (theta nu)⁻¹ * (z + a * theta a)⁻¹ +
          (epsilon * a⁻¹) * theta (epsilon * a⁻¹) := by
  dsimp only
  have hthetaA : theta a ≠ 0 := (map_ne_zero theta).mpr ha
  have hthetaSigma : theta sigma ≠ 0 :=
    (map_ne_zero theta).mpr hsigma
  have hthetaLambda : theta lambda ≠ 0 :=
    (map_ne_zero theta).mpr hlambda
  have hthetaNu : theta nu ≠ 0 := (map_ne_zero theta).mpr hnu
  have hthetaSigmaFirst :
      theta sigma * theta a = 1 + theta lambda := by
    have h := congrArg theta hsigmaFirst
    simpa only [map_mul, map_add, map_one] using h
  have hthetaSigmaZ : theta sigma * z = a * theta lambda := by
    apply mul_left_cancel₀ hsigma
    calc
      sigma * (theta sigma * z) =
          sigma * theta sigma * z := by ring
      _ = (1 + lambda) * theta lambda := hsigmaSecond
      _ = (sigma * a) * theta lambda := by rw [hsigmaFirst]
      _ = sigma * (a * theta lambda) := by ring
  have hlambdaCoordinateMul :
      theta lambda * (z + a * theta a) = z := by
    calc
      theta lambda * (z + a * theta a) =
          theta lambda * z +
            (theta sigma * z) * theta a := by
              rw [hthetaSigmaZ]
              ring
      _ = theta lambda * z + z * (1 + theta lambda) := by
        calc
          theta lambda * z + theta sigma * z * theta a =
              theta lambda * z + z * (theta sigma * theta a) := by ring
          _ = theta lambda * z + z * (1 + theta lambda) := by
            rw [hthetaSigmaFirst]
      _ = z := by
        ring_nf
        simp only [CharTwo.two_eq_zero, mul_zero, zero_add]
  have hlambdaCoordinate :
      theta lambda = z * (z + a * theta a)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (eq_div_iff hb).2 hlambdaCoordinateMul
  have hsigmaFormula : sigma = (1 + lambda) * a⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (eq_div_iff ha).2 hsigmaFirst
  let epsilon : K := (1 + lambda) * (lambda⁻¹ + nu⁻¹)
  have hfirst :
      sigma * (lambda⁻¹ + nu⁻¹) = epsilon * a⁻¹ := by
    rw [hsigmaFormula]
    simp only [epsilon]
    ring
  refine ⟨hlambdaCoordinate, hfirst, ?_⟩
  have hthetaSigmaFormula :
      theta sigma = (1 + theta lambda) * (theta a)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (eq_div_iff hthetaA).2 hthetaSigmaFirst
  have hratio :
      a * theta a * (z + a * theta a)⁻¹ = 1 + theta lambda := by
    rw [hlambdaCoordinate]
    field_simp [hb]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  have hthetaEpsilon :
      theta epsilon =
        (1 + theta lambda) *
          ((theta lambda)⁻¹ + (theta nu)⁻¹) := by
    simp only [epsilon, map_mul, map_add, map_one, map_inv₀]
  have hleft :
      sigma * theta sigma *
          (lambda⁻¹ * theta lambda⁻¹ +
            nu⁻¹ * theta lambda⁻¹) =
        (epsilon * a⁻¹) * theta sigma * (theta lambda)⁻¹ := by
    calc
      sigma * theta sigma *
          (lambda⁻¹ * theta lambda⁻¹ +
            nu⁻¹ * theta lambda⁻¹) =
          (sigma * (lambda⁻¹ + nu⁻¹)) * theta sigma *
            (theta lambda)⁻¹ := by
              simp only [map_inv₀]
              ring
      _ = (epsilon * a⁻¹) * theta sigma * (theta lambda)⁻¹ := by
        rw [hfirst]
  have hfirstTheta :
      (epsilon * a⁻¹) * theta (epsilon * a⁻¹) =
        (epsilon * a⁻¹) * theta epsilon * (theta a)⁻¹ := by
    simp only [map_mul, map_inv₀]
    ring
  have hcore :
      (epsilon * a⁻¹) * ((1 + theta lambda) * (theta a)⁻¹) *
          (theta lambda)⁻¹ =
        epsilon * (theta nu)⁻¹ * (z + a * theta a)⁻¹ +
          (epsilon * a⁻¹) * theta epsilon * (theta a)⁻¹ := by
    calc
      (epsilon * a⁻¹) * ((1 + theta lambda) * (theta a)⁻¹) *
            (theta lambda)⁻¹ =
          epsilon * a⁻¹ * (theta a)⁻¹ *
            ((1 + theta lambda) * (theta lambda)⁻¹) := by ring
      _ = epsilon * a⁻¹ * (theta a)⁻¹ *
          ((1 + theta lambda) * (theta nu)⁻¹ + theta epsilon) := by
            rw [hthetaEpsilon]
            ring_nf
            simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
      _ = epsilon * (theta nu)⁻¹ * (z + a * theta a)⁻¹ +
          (epsilon * a⁻¹) * theta epsilon * (theta a)⁻¹ := by
            rw [← hratio]
            field_simp [ha, hthetaA, hthetaNu, hb]
  rw [hleft, hthetaSigmaFormula, hfirstTheta]
  exact hcore

set_option maxHeartbeats 800000 in
/-- Group-facing contract for the preceding field core.  The `hcoord` fields
are exactly the output of the Bruhat-coordinate and structure-family helpers
after the aligned normalization `g = pair 1 1`. -/
public theorem aligned_generic_alpha_of_bruhat_data
    {K F : Type*} [Field K] [CharP K 2] [Group F]
    (theta : K ≃+* K) (pair : K → K → F)
    (alpha : F → F)
    (a z sigma lambda nu p q : K)
    (ha : a ≠ 0)
    (hb : z + a * theta a ≠ 0)
    (hsigma : sigma ≠ 0) (hlambda : lambda ≠ 0) (hnu : nu ≠ 0)
    (hcoordFirst : sigma * a = 1 + lambda)
    (hcoordSecond :
      sigma * theta sigma * z = (1 + lambda) * theta lambda)
    (hcoordAlpha :
      alpha (pair a z) =
        pair (sigma * (p + q))
          (sigma * theta sigma *
            (q * theta q + p * theta q)))
    (hp : p = nu⁻¹) (hq : q = lambda⁻¹) :
    let epsilon : K := (1 + lambda) * (lambda⁻¹ + nu⁻¹)
    theta lambda = z * (z + a * theta a)⁻¹ ∧
      alpha (pair a z) =
        pair (epsilon * a⁻¹)
          (epsilon * (theta nu)⁻¹ * (z + a * theta a)⁻¹ +
            (epsilon * a⁻¹) * theta (epsilon * a⁻¹)) := by
  dsimp only
  have hcore := aligned_generic_coordinate_core theta a z sigma lambda nu
    ha hsigma hlambda hnu hb hcoordFirst hcoordSecond
  let epsilon : K := (1 + lambda) * (lambda⁻¹ + nu⁻¹)
  refine ⟨hcore.1, ?_⟩
  have hfirst := hcore.2.1
  have hsecond := hcore.2.2
  rw [hcoordAlpha, hp, hq]
  apply congrArg₂ pair
  · simpa only [add_comm] using hfirst
  · exact hsecond

/-- The downstream-facing proposition produced by one generic XI.11.13(b)
application.  It is intentionally a proposition: the quantified scalars may
be unpacked without crossing Lean's `Prop` elimination boundary. -/
public def AlignedGenericAlphaData
    {K F : Type*} [Field K] [Group F]
    (theta : K ≃+* K) (pair : K → K → F) (alpha : F → F)
    (a z : K) : Prop :=
  ∃ lambda nu : K,
    lambda ≠ 0 ∧ nu ≠ 0 ∧
    theta lambda = z * (z + a * theta a)⁻¹ ∧
    nu * theta nu =
      lambda ^ 2 * (theta lambda) ^ 2 + lambda * theta lambda ∧
    (let epsilon : K := (1 + lambda) * (lambda⁻¹ + nu⁻¹)
     alpha (pair a z) =
       pair (epsilon * a⁻¹)
         (epsilon * (theta nu)⁻¹ * (z + a * theta a)⁻¹ +
           (epsilon * a⁻¹) * theta (epsilon * a⁻¹)))

set_option maxHeartbeats 800000 in
/-- A non-circular group-facing form of the generic XI.11.13(b) data.  The
orbit cover is an explicit input, and the conclusion records only the raw
Bruhat parameters used by `aligned_generic_alpha_of_bruhat_data`. -/
public theorem aligned_generic_bruhat_data_of_family
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
    (j g : F) (hj : j = pair 0 1) (hg : g = pair 1 1)
    (alpha : F → F)
    (halphaActor : ∀ d : D, ∀ x : F, x ≠ 1 →
      alpha (d • x) = d⁻¹ • alpha x)
    (hcover : ∀ x : F, x ≠ 1 →
      (∃ d : D, d⁻¹ • x = j) ∨
      (∃ d : D, d⁻¹ • x = g) ∨
      (∃ d : D, d⁻¹ • x = g⁻¹) ∨
      ∃ d h : D, h ≠ 1 ∧ d⁻¹ • x = g⁻¹ * (h⁻¹ • g))
    (hfamily : ∀ h : D, h ≠ 1 →
      ∃ k : D,
        h⁻¹ • ((h⁻¹ • j) * j) = k⁻¹ • j ∧
          alpha (g⁻¹ * (h⁻¹ • g)) = (k • g⁻¹) * (h • g))
    (A Z : K) (hA : A ≠ 0) (hZ : Z ≠ 0)
    (hB : Z + A * theta A ≠ 0) :
    ∃ sigma lambda nu p q : K,
      sigma ≠ 0 ∧ lambda ≠ 0 ∧ nu ≠ 0 ∧
      sigma * A = 1 + lambda ∧
      sigma * theta sigma * Z = (1 + lambda) * theta lambda ∧
      nu * theta nu =
        lambda ^ 2 * (theta lambda) ^ 2 + lambda * theta lambda ∧
      p = nu⁻¹ ∧ q = lambda⁻¹ ∧
      alpha (pair A Z) =
        pair (sigma * (p + q))
          (sigma * theta sigma *
            (q * theta q + p * theta q)) := by
  have hginv : g⁻¹ = pair 1 0 := by
    have hpairInv : pair 1 0 = (pair 1 1)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [hmul, map_one]
      simpa only [zero_add, mul_one, CharTwo.add_self_eq_zero] using hone
    exact (congrArg Inv.inv hg).trans (by simpa using hpairInv.symm)
  have hx : pair A Z ≠ 1 := by
    intro hx
    have hcoord := hinj A Z 0 0 (hx.trans hone.symm)
    exact hA (by simpa using hcoord.1)
  obtain hcase | hcase | hcase | hcase := hcover (pair A Z) hx
  · obtain ⟨d, hd⟩ := hcase
    rw [hactor, hj] at hd
    have hcoord := hinj _ _ _ _ hd
    have hs : (eD (d⁻¹) : K) ≠ 0 := (eD (d⁻¹)).ne_zero
    exact False.elim (hA ((mul_eq_zero.mp hcoord.1).resolve_left hs))
  · obtain ⟨d, hd⟩ := hcase
    rw [hactor, hg] at hd
    have hcoord := hinj _ _ _ _ hd
    let sigma : K := (eD (d⁻¹) : K)
    have hs : sigma ≠ 0 := (eD (d⁻¹)).ne_zero
    have hts : theta sigma ≠ 0 := (map_ne_zero theta).mpr hs
    have hAcoord : sigma * A = 1 := by simpa [sigma] using hcoord.1
    have hZcoord : sigma * theta sigma * Z = 1 := by
      simpa [sigma] using hcoord.2
    have hAeq : A = sigma⁻¹ := by
      calc
        A = 1 * A := (one_mul A).symm
        _ = (sigma⁻¹ * sigma) * A := by rw [inv_mul_cancel₀ hs]
        _ = sigma⁻¹ * (sigma * A) := by ring
        _ = sigma⁻¹ := by rw [hAcoord, mul_one]
    have hthetaAeq : theta A = (theta sigma)⁻¹ := by
      rw [hAeq, map_inv₀]
    have hZeq : Z = (sigma * theta sigma)⁻¹ := by
      calc
        Z = 1 * Z := (one_mul Z).symm
        _ = (sigma * theta sigma)⁻¹ *
            (sigma * theta sigma) * Z := by
          rw [inv_mul_cancel₀ (mul_ne_zero hs hts)]
        _ = (sigma * theta sigma)⁻¹ *
            (sigma * theta sigma * Z) := by ring
        _ = (sigma * theta sigma)⁻¹ := by rw [hZcoord, mul_one]
    apply False.elim
    apply hB
    rw [hZeq, hAeq, map_inv₀, mul_inv]
    exact CharTwo.add_self_eq_zero _
  · obtain ⟨d, hd⟩ := hcase
    rw [hactor, hginv] at hd
    have hcoord := hinj _ _ _ _ hd
    have hs : (eD (d⁻¹) : K) ≠ 0 := (eD (d⁻¹)).ne_zero
    have hts : theta (eD (d⁻¹) : K) ≠ 0 :=
      (map_ne_zero theta).mpr hs
    exact False.elim (hZ ((mul_eq_zero.mp hcoord.2).resolve_left
      (mul_ne_zero hs hts)))
  · obtain ⟨d, h, hh, hd⟩ := hcase
    obtain ⟨k, hcentral, halphaFamily⟩ := hfamily h hh
    let sigma : K := (eD (d⁻¹) : K)
    let lambda : K := (eD (h⁻¹) : K)
    let nu : K := (eD (k⁻¹) : K)
    let p : K := (eD k : K)
    let q : K := (eD h : K)
    have hsigma : sigma ≠ 0 := (eD (d⁻¹)).ne_zero
    have hlambda : lambda ≠ 0 := (eD (h⁻¹)).ne_zero
    have hnu : nu ≠ 0 := (eD (k⁻¹)).ne_zero
    have hnorm : nu * theta nu =
        lambda ^ 2 * (theta lambda) ^ 2 + lambda * theta lambda := by
      rw [hj, hactor, hmul, hactor, hactor] at hcentral
      have hsecond := (hinj _ _ _ _ hcentral).2
      have hsecond' : nu * theta nu =
          (lambda * theta lambda) * (lambda * theta lambda + 1) := by
        simpa [lambda, nu] using hsecond.symm
      calc
        nu * theta nu =
            (lambda * theta lambda) * (lambda * theta lambda + 1) := hsecond'
        _ = lambda ^ 2 * (theta lambda) ^ 2 +
            lambda * theta lambda := by ring
    have hdcoord := hd
    rw [hactor, hginv, hg, hactor, hmul] at hdcoord
    have hcoord := hinj _ _ _ _ hdcoord
    have hcoordFirst : sigma * A = 1 + lambda := by
      simpa [sigma, lambda] using hcoord.1
    have hcoordSecond :
        sigma * theta sigma * Z = (1 + lambda) * theta lambda := by
      calc
        sigma * theta sigma * Z =
            lambda * theta lambda + theta lambda := by
          simpa [sigma, lambda] using hcoord.2
        _ = (1 + lambda) * theta lambda := by ring
    have halphaCoord :
        alpha (pair A Z) =
          pair (sigma * (p + q))
            (sigma * theta sigma *
              (q * theta q + p * theta q)) := by
      have halphaOrbit := halphaActor d⁻¹ (pair A Z) hx
      have halphaEq : alpha (pair A Z) =
          d⁻¹ • alpha (g⁻¹ * (h⁻¹ • g)) := by
        calc
          alpha (pair A Z) = d⁻¹ • (d • alpha (pair A Z)) :=
            (inv_smul_smul d (alpha (pair A Z))).symm
          _ = d⁻¹ • alpha (d⁻¹ • pair A Z) := by
            rw [show d • alpha (pair A Z) =
                alpha (d⁻¹ • pair A Z) by
              simpa only [inv_inv] using halphaOrbit.symm]
          _ = d⁻¹ • alpha (g⁻¹ * (h⁻¹ • g)) := by rw [hd]
      rw [halphaEq, halphaFamily, hginv, hg, hactor, hactor, hmul,
        hactor]
      simp [sigma, p, q]
    refine ⟨sigma, lambda, nu, p, q, hsigma, hlambda, hnu,
      hcoordFirst, hcoordSecond, hnorm, ?_, ?_, halphaCoord⟩
    · simp [p, nu]
    · simp [q, lambda]

set_option maxHeartbeats 800000 in
/-- The checked orbit-family extraction followed by the field-algebra
translation, with all intermediate Bruhat scalars hidden. -/
public theorem aligned_generic_alpha_data_of_family
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
    (j g : F) (hj : j = pair 0 1) (hg : g = pair 1 1)
    (alpha : F → F)
    (halphaActor : ∀ d : D, ∀ x : F, x ≠ 1 →
      alpha (d • x) = d⁻¹ • alpha x)
    (hcover : ∀ x : F, x ≠ 1 →
      (∃ d : D, d⁻¹ • x = j) ∨
      (∃ d : D, d⁻¹ • x = g) ∨
      (∃ d : D, d⁻¹ • x = g⁻¹) ∨
      ∃ d h : D, h ≠ 1 ∧ d⁻¹ • x = g⁻¹ * (h⁻¹ • g))
    (hfamily : ∀ h : D, h ≠ 1 →
      ∃ k : D,
        h⁻¹ • ((h⁻¹ • j) * j) = k⁻¹ • j ∧
          alpha (g⁻¹ * (h⁻¹ • g)) = (k • g⁻¹) * (h • g))
    (A Z : K) (hA : A ≠ 0) (hZ : Z ≠ 0)
    (hB : Z + A * theta A ≠ 0) :
    AlignedGenericAlphaData theta pair alpha A Z := by
  obtain ⟨sigma, lambda, nu, p, q, hsigma, hlambda, hnu,
      hcoordFirst, hcoordSecond, hnorm, hp, hq, halphaCoord⟩ :=
    aligned_generic_bruhat_data_of_family theta pair eD hone hinj hmul
      hactor j g hj hg alpha halphaActor hcover hfamily A Z hA hZ hB
  have hformula := aligned_generic_alpha_of_bruhat_data theta pair alpha
    A Z sigma lambda nu p q hA hB hsigma hlambda hnu hcoordFirst
      hcoordSecond halphaCoord hp hq
  exact ⟨lambda, nu, hlambda, hnu, hformula.1, hnorm, hformula.2⟩

set_option maxHeartbeats 800000 in
/-- The two generic XI.11.13 inputs used by XI.11.14 are admissible whenever
the field element `a` is nonzero and nonunit.  This layer deliberately leaves
the XI.11.10 product equation to its caller. -/
public theorem aligned_xi1114_two_generic_inputs
    {K F : Type*} [Field K] [CharP K 2]
    [Group F]
    (theta : K ≃+* K)
    (hnormInjective : Function.Injective (fun x : K => x * theta x))
    (pair : K → K → F) (alpha : F → F)
    (a : K) (ha : a ≠ 0) (haOne : a ≠ 1)
    (hgeneric : ∀ A Z : K, A ≠ 0 → Z ≠ 0 →
      Z + A * theta A ≠ 0 →
      AlignedGenericAlphaData theta pair alpha A Z) :
    AlignedGenericAlphaData theta pair alpha 1
        (1 + (a * theta.symm a)⁻¹) ∧
      AlignedGenericAlphaData theta pair alpha 1
        (a * theta.symm a)⁻¹ := by
  let t : K := theta.symm a
  let n : K := a * t
  have ht : t ≠ 0 := (map_ne_zero theta.symm).mpr ha
  have hn : n ≠ 0 := mul_ne_zero ha ht
  have hnOne : n ≠ 1 := by
    intro h
    have hnormEq : t * theta t = 1 * theta 1 := by
      simpa [t, n, mul_comm] using h
    have htOne : t = 1 := hnormInjective hnormEq
    exact haOne (by simpa [t] using congrArg (fun x => theta x) htOne)
  have hZ₁ : 1 + n⁻¹ ≠ 0 := by
    intro h
    apply hnOne
    apply inv_eq_one.mp
    apply add_left_cancel (a := (1 : K))
    simp only [h, CharTwo.add_self_eq_zero]
  have hB₁ : (1 + n⁻¹) + (1 : K) ≠ 0 := by
    intro h
    apply inv_ne_zero hn
    calc
      n⁻¹ = (1 + n⁻¹) + 1 := by
        ring_nf
        simp only [CharTwo.two_eq_zero, zero_add]
      _ = 0 := h
  have hZ₂ : n⁻¹ ≠ 0 := inv_ne_zero hn
  have hB₂ : n⁻¹ + (1 : K) ≠ 0 := by
    simpa [add_comm] using hZ₁
  constructor
  · exact hgeneric 1 (1 + n⁻¹) (by simp) hZ₁ (by simpa using hB₁)
  · exact hgeneric 1 n⁻¹ (by simp) hZ₂ (by simpa using hB₂)

set_option maxHeartbeats 800000 in
/-- The scalar content of XI.11.10(6) after expanding the two aligned
XI.11.13(b) formulas.  The first two hypotheses are the two coordinates of
`t⁻¹ • alpha (pair 1 n⁻¹) =
  alpha (pair 1 (1 + n⁻¹)) * pair 1 0`. -/
public theorem aligned_product_coordinate_equation_core
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K)
    (t n eta epsilon mu nu : K)
    (ht : t ≠ 0) (hn : n ≠ 0)
    (hnorm : n = t * theta t)
    (hfirst : t⁻¹ * epsilon = eta + 1)
    (hsecond :
      n⁻¹ *
          (epsilon * (theta nu)⁻¹ * n * (1 + n)⁻¹ +
            epsilon * theta epsilon) =
        eta * (theta mu)⁻¹ * n + eta * theta eta + eta) :
    1 + eta * (theta mu)⁻¹ * n + theta eta =
      epsilon * (theta nu)⁻¹ * (1 + n)⁻¹ := by
  have hthetaT : theta t ≠ 0 := (map_ne_zero theta).mpr ht
  have hthetaFirst :
      theta t⁻¹ * theta epsilon = theta eta + 1 := by
    have h := congrArg theta hfirst
    simpa only [map_mul, map_inv₀, map_add, map_one] using h
  have hnormInv : t⁻¹ * theta t⁻¹ = n⁻¹ := by
    rw [map_inv₀, hnorm, mul_inv]
  have hcross :
      n⁻¹ * epsilon * theta epsilon =
        (eta + 1) * (theta eta + 1) := by
    calc
      n⁻¹ * epsilon * theta epsilon =
          (t⁻¹ * theta t⁻¹) * epsilon * theta epsilon := by
            rw [hnormInv]
      _ = (t⁻¹ * epsilon) *
          (theta t⁻¹ * theta epsilon) := by ring
      _ = (eta + 1) * (theta eta + 1) := by
        rw [hfirst, hthetaFirst]
  have hsecond' :
      epsilon * (theta nu)⁻¹ * (1 + n)⁻¹ +
          (eta + 1) * (theta eta + 1) =
        eta * (theta mu)⁻¹ * n + eta * theta eta + eta := by
    calc
      epsilon * (theta nu)⁻¹ * (1 + n)⁻¹ +
          (eta + 1) * (theta eta + 1) =
        n⁻¹ *
            (epsilon * (theta nu)⁻¹ * n * (1 + n)⁻¹) +
          n⁻¹ * epsilon * theta epsilon := by
            rw [hcross]
            field_simp [hn]
      _ = n⁻¹ *
          (epsilon * (theta nu)⁻¹ * n * (1 + n)⁻¹ +
            epsilon * theta epsilon) := by ring
      _ = eta * (theta mu)⁻¹ * n + eta * theta eta + eta := hsecond
  calc
    1 + eta * (theta mu)⁻¹ * n + theta eta =
        (eta * (theta mu)⁻¹ * n + eta * theta eta + eta) +
          (eta + 1) * (theta eta + 1) := by
            ring_nf
            simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
    _ = (epsilon * (theta nu)⁻¹ * (1 + n)⁻¹ +
          (eta + 1) * (theta eta + 1)) +
            (eta + 1) * (theta eta + 1) := by rw [hsecond']
    _ = epsilon * (theta nu)⁻¹ * (1 + n)⁻¹ := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

set_option maxHeartbeats 800000 in
/-- Rewrites XI.11.14 equation (6) into the normalized coordinate equation
consumed by the factor calculation. -/
public theorem aligned_normalized_coordinate_equation
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K)
    (xi mu nu eta epsilon n : K)
    (hxi : xi ≠ 0) (hmu : mu ≠ 0)
    (hxiCoordinate : theta xi = (1 + n)⁻¹)
    (hnu : nu = mu * xi ^ 3)
    (hsource :
      1 + eta * (theta mu)⁻¹ * n + theta eta =
        epsilon * (theta nu)⁻¹ * (1 + n)⁻¹) :
    eta + eta * (theta xi)⁻¹ +
        (1 + theta eta) * theta mu =
      epsilon * (theta xi)⁻¹ ^ 2 := by
  have hthetaXi : theta xi ≠ 0 := (map_ne_zero theta).mpr hxi
  have hthetaMu : theta mu ≠ 0 := (map_ne_zero theta).mpr hmu
  have hOneAddN : 1 + n ≠ 0 := by
    intro h
    have hzero : theta xi = 0 := by rw [hxiCoordinate, h, inv_zero]
    exact hthetaXi hzero
  have hthetaXiInv : (theta xi)⁻¹ = 1 + n := by
    rw [hxiCoordinate, inv_inv]
  have hn : n = (theta xi)⁻¹ + 1 := by
    rw [hthetaXiInv]
    calc
      n = n + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (1 + n) + 1 := by abel
  have hthetaNu : theta nu = theta mu * (theta xi) ^ 3 := by
    rw [hnu, map_mul, map_pow]
  have hsource' := hsource
  rw [hn, hthetaNu] at hsource'
  have hdenom :
      (1 + ((theta xi)⁻¹ + 1))⁻¹ = theta xi := by
    rw [show 1 + ((theta xi)⁻¹ + 1) = (theta xi)⁻¹ by
      calc
        1 + ((theta xi)⁻¹ + 1) = (1 + 1) + (theta xi)⁻¹ := by abel
        _ = (theta xi)⁻¹ := by
          rw [CharTwo.add_self_eq_zero, zero_add], inv_inv]
  rw [hdenom] at hsource'
  field_simp [hthetaXi, hthetaMu] at hsource' ⊢
  ring_nf at hsource' ⊢
  exact hsource'

/-- The exact scalar package immediately before the existing
`xi1115_theta_factor_of_coordinate_equations` calculation. -/
@[expose] public def AlignedThetaCoordinateData
    {K : Type*} [Field K]
    (theta : K ≃+* K) (a : K) : Prop :=
  ∃ xi mu nu eta epsilon : K,
    xi ≠ 0 ∧ mu ≠ 0 ∧ nu ≠ 0 ∧
    theta xi = (1 + a * theta.symm a)⁻¹ ∧
    mu * theta mu =
      xi⁻¹ ^ 2 * (theta xi)⁻¹ ^ 2 + xi⁻¹ * (theta xi)⁻¹ ∧
    nu * theta nu =
      xi ^ 2 * (theta xi) ^ 2 + xi * theta xi ∧
    eta = (1 + xi⁻¹) * (xi + mu⁻¹) ∧
    epsilon = (1 + xi) * (xi⁻¹ + nu⁻¹) ∧
    eta + eta * (theta xi)⁻¹ +
        (1 + theta eta) * theta mu =
      epsilon * (theta xi)⁻¹ ^ 2

/-- Twisted-norm injectivity is unchanged when the field automorphism is
replaced by its inverse. -/
public theorem twisted_norm_symm_injective
    {K : Type*} [Field K]
    (theta : K ≃+* K)
    (h : Function.Injective (fun x : K => x * theta x)) :
    Function.Injective (fun x : K => x * theta.symm x) := by
  intro x y hxy
  have hpre : theta.symm x = theta.symm y := by
    apply h
    simpa only [theta.apply_symm_apply, mul_comm] using hxy
  simpa only [theta.apply_symm_apply] using congrArg theta hpre


set_option maxHeartbeats 800000 in
/-- The aligned specialization of XI.11.10(6).  This packages the short
group calculation that produces the `hproduct` input of
`aligned_theta_coordinate_data_of_generic_product`. -/
public theorem aligned_generic_product_identity_of_alpha_laws
    {K F D : Type*} [Field K] [CharP K 2]
    [Group F] [Group D] [MulDistribMulAction D F]
    (theta : K ≃+* K)
    (pair : K → K → F) (eD : D ≃* Kˣ)
    (hone : pair 0 0 = 1)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w = pair (a + b) (z + w + a * theta b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z = pair ((eD d : K) * a)
        ((eD d : K) * theta (eD d : K) * z))
    (j g : F) (hj : j = pair 0 1) (hg : g = pair 1 1)
    (alpha beta : F → F) (gamma : F → D)
    (halphaCov : ∀ d : D, ∀ x : F, x ≠ 1 →
      alpha (d • x) = d⁻¹ • alpha x)
    (halphaGInv : alpha g⁻¹ = j)
    (hbetaJ : beta j = g)
    (hgammaJ : gamma j = 1)
    (halphaJ : alpha j = g⁻¹)
    (hproductLaw : ∀ x₁ x₂ : F,
      x₁ ≠ 1 → x₂ ≠ 1 → x₁ * x₂ ≠ 1 →
      alpha x₁ * beta x₂ ≠ 1 →
      alpha (x₁ * x₂) =
        gamma x₂ • alpha (alpha x₁ * beta x₂) * alpha x₂)
    (a : K) (ha : a ≠ 0)
    (d : D) (hd : (eD d : K) = theta.symm a) :
    d⁻¹ • alpha (pair 1 (a * theta.symm a)⁻¹) =
      alpha (pair 1 (1 + (a * theta.symm a)⁻¹)) * pair 1 0 := by
  let t : K := theta.symm a
  let n : K := a * t
  have ht : t ≠ 0 := (map_ne_zero theta.symm).mpr ha
  have hthetaT : theta t = a := by simp [t]
  have hn : n ≠ 0 := mul_ne_zero ha ht
  have hnorm : n = t * theta t := by rw [hthetaT]; simp [n, mul_comm]
  have hginv : g⁻¹ = pair 1 0 := by
    apply inv_eq_of_mul_eq_one_right
    rw [hg, hmul]
    convert hone using 1 ;
      simp only [map_one, mul_one, add_zero, CharTwo.add_self_eq_zero]
  have hdInv : (eD (d⁻¹) : K) = t⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, hd, t]
  have hscale : t⁻¹ * theta t⁻¹ = n⁻¹ := by
    rw [map_inv₀, hnorm, mul_inv]
  have hpairNeOneOfFirst (A Z : K) (hA : A ≠ 0) : pair A Z ≠ 1 := by
    intro h
    have hcoord := hinj A Z 0 0 (h.trans hone.symm)
    exact hA hcoord.1
  have hjne : j ≠ 1 := by
    intro h
    have hcoord := hinj 0 1 0 0 ((hj.symm.trans h).trans hone.symm)
    exact one_ne_zero hcoord.2
  have hgne : g ≠ 1 := by
    rw [hg]
    exact hpairNeOneOfFirst 1 1 one_ne_zero
  have hx₁ne : pair t 0 ≠ 1 := hpairNeOneOfFirst t 0 ht
  have hxprodNe : pair t 0 * j ≠ 1 := by
    rw [hj, hmul]
    apply hpairNeOneOfFirst
    simpa only [add_zero] using ht
  have hx₁Action : d • g⁻¹ = pair t 0 := by
    rw [hginv, hactor, hd]
    apply congrArg₂ pair
    · simp only [mul_one, t]
    · simp only [mul_zero]
  have halphaX₁ : alpha (pair t 0) = pair 0 n⁻¹ := by
    calc
      alpha (pair t 0) = alpha (d • g⁻¹) := by rw [hx₁Action]
      _ = d⁻¹ • alpha g⁻¹ := halphaCov d g⁻¹ (inv_ne_one.mpr hgne)
      _ = d⁻¹ • j := by rw [halphaGInv]
      _ = pair 0 n⁻¹ := by
        rw [hj, hactor]
        apply congrArg₂ pair
        · simp only [mul_zero]
        · simp only [hdInv, mul_one]
          exact hscale
  have hmiddle : alpha (pair t 0) * beta j = pair 1 (1 + n⁻¹) := by
    rw [halphaX₁, hbetaJ, hg, hmul]
    apply congrArg₂ pair
    · simp only [zero_add]
    · simp only [map_one, zero_mul, add_zero]
      exact add_comm n⁻¹ 1
  have hmiddleNe : alpha (pair t 0) * beta j ≠ 1 := by
    rw [hmiddle]
    exact hpairNeOneOfFirst 1 (1 + n⁻¹) one_ne_zero
  have hxprod : pair t 0 * j = d • pair 1 n⁻¹ := by
    rw [hj, hmul, hactor, hd]
    apply congrArg₂ pair
    · simp only [add_zero, mul_one, t]
    · simp only [map_zero, mul_zero, add_zero, zero_add]
      calc
        1 = n * n⁻¹ := (mul_inv_cancel₀ hn).symm
        _ = t * theta t * n⁻¹ := by rw [hnorm]
  have hfunctional := hproductLaw (pair t 0) j hx₁ne hjne hxprodNe hmiddleNe
  rw [hmiddle, hgammaJ, one_smul, halphaJ, hginv] at hfunctional
  calc
    d⁻¹ • alpha (pair 1 n⁻¹) =
        alpha (d • pair 1 n⁻¹) := by
          rw [halphaCov d (pair 1 n⁻¹)
            (hpairNeOneOfFirst 1 n⁻¹ one_ne_zero)]
    _ = alpha (pair t 0 * j) := by rw [hxprod]
    _ = alpha (pair 1 (1 + n⁻¹)) * pair 1 0 := hfunctional

set_option maxHeartbeats 800000 in
/-- Two generic XI.11.13(b) records, together with the one XI.11.10(6)
product identity, give all scalar equations used by XI.11.14. -/
public theorem aligned_theta_coordinate_data_of_generic_product
    {K F D : Type*} [Field K] [CharP K 2]
    [Group F] [Group D] [MulDistribMulAction D F]
    (theta : K ≃+* K)
    (hnormInjective : Function.Injective (fun x : K => x * theta x))
    (pair : K → K → F) (eD : D ≃* Kˣ)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w = pair (a + b) (z + w + a * theta b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z = pair ((eD d : K) * a)
        ((eD d : K) * theta (eD d : K) * z))
    (alpha : F → F)
    (a : K) (ha : a ≠ 0)
    (hdataEta : AlignedGenericAlphaData theta pair alpha 1
      (1 + (a * theta.symm a)⁻¹))
    (hdataEpsilon : AlignedGenericAlphaData theta pair alpha 1
      (a * theta.symm a)⁻¹)
    (d : D) (hd : (eD d : K) = theta.symm a)
    (hproduct :
      d⁻¹ • alpha (pair 1 (a * theta.symm a)⁻¹) =
        alpha (pair 1 (1 + (a * theta.symm a)⁻¹)) * pair 1 0) :
    AlignedThetaCoordinateData theta a := by
  let t : K := theta.symm a
  let n : K := a * t
  have ht : t ≠ 0 := (map_ne_zero theta.symm).mpr ha
  have hthetaT : theta t = a := by simp [t]
  have hn : n ≠ 0 := mul_ne_zero ha ht
  have hnorm : n = t * theta t := by rw [hthetaT]; simp [n, mul_comm]
  change AlignedGenericAlphaData theta pair alpha 1 (1 + n⁻¹) at hdataEta
  change AlignedGenericAlphaData theta pair alpha 1 n⁻¹ at hdataEpsilon
  obtain ⟨kappa, mu, hkappa, hmu, hkappaCoordinateRaw,
      hmuNormRaw, hAlphaEtaRaw⟩ := hdataEta
  obtain ⟨xi, nu, hxi, hnu, hxiCoordinateRaw,
      hnuNorm, hAlphaEpsilonRaw⟩ := hdataEpsilon
  let eta : K := (1 + kappa) * (kappa⁻¹ + mu⁻¹)
  let epsilon : K := (1 + xi) * (xi⁻¹ + nu⁻¹)
  have hkappaCoordinate0 :
      theta kappa = (1 + n⁻¹) * ((1 + n⁻¹) + 1)⁻¹ := by
    simpa only [one_mul, map_one] using hkappaCoordinateRaw
  have hxiCoordinate0 :
      theta xi = n⁻¹ * (n⁻¹ + 1)⁻¹ := by
    simpa only [one_mul, map_one] using hxiCoordinateRaw
  have hAlphaEta0 :
      alpha (pair 1 (1 + n⁻¹)) =
        pair eta
          (eta * (theta mu)⁻¹ * ((1 + n⁻¹) + 1)⁻¹ +
            eta * theta eta) := by
    simpa only [eta, one_mul, mul_one, map_one, inv_one] using hAlphaEtaRaw
  have hAlphaEpsilon0 :
      alpha (pair 1 n⁻¹) =
        pair epsilon
          (epsilon * (theta nu)⁻¹ * (n⁻¹ + 1)⁻¹ +
            epsilon * theta epsilon) := by
    simpa only [epsilon, one_mul, mul_one, map_one, inv_one] using
      hAlphaEpsilonRaw
  have hdenEta : ((1 + n⁻¹) + 1)⁻¹ = n := by
    rw [show (1 + n⁻¹) + 1 = n⁻¹ by
      calc
        (1 + n⁻¹) + 1 = (1 + 1) + n⁻¹ := by abel
        _ = n⁻¹ := by rw [CharTwo.add_self_eq_zero, zero_add], inv_inv]
  have hkappaCoordinate : theta kappa = 1 + n := by
    rw [hdenEta] at hkappaCoordinate0
    calc
      theta kappa = (1 + n⁻¹) * n := hkappaCoordinate0
      _ = 1 + n := by field_simp [hn]; ring
  have hAlphaEta :
      alpha (pair 1 (1 + n⁻¹)) =
        pair eta
          (eta * (theta mu)⁻¹ * n + eta * theta eta) := by
    simpa only [hdenEta] using hAlphaEta0
  have hnOne : n ≠ 1 := by
    intro hnOne
    have hzero : theta xi = 0 := by
      rw [hxiCoordinate0, hnOne]
      simp only [inv_one, CharTwo.add_self_eq_zero, inv_zero, mul_zero]
    exact (map_ne_zero theta).mpr hxi hzero
  have hOneAddN : 1 + n ≠ 0 := by
    intro h
    apply hnOne
    exact ((eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq n)).symm
  have hdenEpsilon : (n⁻¹ + 1)⁻¹ = n * (1 + n)⁻¹ := by
    field_simp [hn, hOneAddN]
  have hxiCoordinate : theta xi = (1 + n)⁻¹ := by
    rw [hdenEpsilon] at hxiCoordinate0
    calc
      theta xi = n⁻¹ * (n * (1 + n)⁻¹) := hxiCoordinate0
      _ = (1 + n)⁻¹ := by field_simp [hn]
  have hAlphaEpsilon :
      alpha (pair 1 n⁻¹) =
        pair epsilon
          (epsilon * (theta nu)⁻¹ * n * (1 + n)⁻¹ +
            epsilon * theta epsilon) := by
    rw [hdenEpsilon] at hAlphaEpsilon0
    simpa only [mul_assoc] using hAlphaEpsilon0
  have hkappaEq : kappa = xi⁻¹ := by
    apply theta.injective
    rw [hkappaCoordinate, map_inv₀, hxiCoordinate, inv_inv]
  have hmuNorm :
      mu * theta mu =
        xi⁻¹ ^ 2 * (theta xi)⁻¹ ^ 2 + xi⁻¹ * (theta xi)⁻¹ := by
    simpa only [hkappaEq, map_inv₀] using hmuNormRaw
  have hdInv : (eD (d⁻¹) : K) = t⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, hd, t]
  have hscale : t⁻¹ * theta t⁻¹ = n⁻¹ := by
    rw [map_inv₀, hnorm, mul_inv]
  have hproduct' := hproduct
  change d⁻¹ • alpha (pair 1 n⁻¹) =
    alpha (pair 1 (1 + n⁻¹)) * pair 1 0 at hproduct'
  rw [hAlphaEpsilon, hactor, hAlphaEta, hmul] at hproduct'
  simp only [hdInv, map_one, mul_one, add_zero] at hproduct'
  rw [hscale] at hproduct'
  have hproductCoordinates := hinj _ _ _ _ hproduct'
  have hsource := aligned_product_coordinate_equation_core theta
    t n eta epsilon mu nu ht hn hnorm hproductCoordinates.1
      hproductCoordinates.2
  have hthetaXi : theta xi ≠ 0 := (map_ne_zero theta).mpr hxi
  have hnuEq : nu = mu * xi ^ 3 := by
    apply hnormInjective
    change nu * theta nu = (mu * xi ^ 3) * theta (mu * xi ^ 3)
    rw [hnuNorm, map_mul, map_pow]
    rw [show
      mu * xi ^ 3 * (theta mu * theta xi ^ 3) =
          (mu * theta mu) * (xi ^ 3 * theta xi ^ 3) by ring,
      hmuNorm]
    field_simp [hxi, hthetaXi]
    ring_nf
  have hcoordinate := aligned_normalized_coordinate_equation theta
    xi mu nu eta epsilon n hxi hmu hxiCoordinate hnuEq hsource
  refine ⟨xi, mu, nu, eta, epsilon, hxi, hmu, hnu, ?_, hmuNorm,
    hnuNorm, ?_, rfl, hcoordinate⟩
  · simpa [n, t] using hxiCoordinate
  · simp only [eta, hkappaEq, inv_inv]

end XI1115ThetaEquationExtraction
end CFSG.BenderSuzuki.External

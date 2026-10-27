module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
import Mathlib.Tactic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dimension.Free

namespace CFSG
end CFSG
open CFSG

/-!
# Odd nonsplit-torus subgroups fixed by a pure field automorphism

For the standard nonsplit torus in `PGL₂(K)` — the projective image of the
matrices `!![a, b * lam; b, a]` for a nonsquare parameter `lam` — projective
commutation with a pure coefficient automorphism forces the parameter ratio
`a / b` of every fixed element to lie in the fixed subfield `R` of `sigma`.
Consequently an odd subgroup of the torus that is invariant under `sigma`
and projectively centralized by the corresponding pure semilinear element is
contained in the `sigma`-fixed part of the torus, which has exactly
`|R| + 1` elements.  Hence `Nat.card A ∣ Nat.card R + 1`.

A nonsquare chosen in the fixed subfield remains a nonsquare in `K` when the
extension degree `[K : R]` is an odd prime: if `lam = x * x` with `x ∈ K`,
then `x` is integral over `R` with minimal polynomial dividing `X² - C lam`,
so `finrank R R⟮x⟯ ≤ 2`; the tower law `finrank R K = p` then forces
`finrank R R⟮x⟯ = 1` and `x ∈ R`, contradicting nonsquareness in `R`.

This is the nonsplit-torus matrix core needed in the semilinear half of
Bender's Fact 1.10(ii).
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open Polynomial
open scoped MatrixGroups

universe u

/-- The matrix `!![a, b * lam; b, a]` with entries in a field. -/
private def emb {K : Type u} [Field K] (lam a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a, b * lam; b, a]

private lemma emb_det {K : Type u} [Field K] (lam a b : K) :
    (emb lam a b).det = a ^ 2 - b ^ 2 * lam := by
  simp [emb, Matrix.det_fin_two, pow_two, mul_comm, mul_left_comm]

private lemma emb_mul {K : Type u} [Field K] (lam a b c d : K) :
    emb lam a b * emb lam c d = emb lam (a * c + b * d * lam) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The standard nonsplit torus of `PGL₂(K)` with parameter `lam`: the
projective images of the invertible matrices `!![a, b * lam; b, a]`. -/
public def pGammaL2NonsplitTorus (K : Type u) [Field K] (lam : K) :
    Subgroup (PGL2 K) where
  carrier := {x : PGL2 K | ∃ (A : GL (Fin 2) K) (a b : K),
    x = Matrix.ProjGenLinGroup.mk A ∧ (A : Matrix (Fin 2) (Fin 2) K) = emb lam a b}
  one_mem' := by
    refine ⟨1, 1, 0, ?_, ?_⟩
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [emb]
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨A, a, b, hx, hA⟩
    rcases hy with ⟨B, c, d, hy, hB⟩
    refine ⟨A * B, a * c + b * d * lam, a * d + b * c, ?_, ?_⟩
    · rw [hx, hy]
      simp
    · change (A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) =
          emb lam (a * c + b * d * lam) (a * d + b * c)
      rw [hA, hB]
      exact emb_mul lam a b c d
  inv_mem' := by
    intro x hx
    rcases hx with ⟨A, a, b, hx, hA⟩
    let d := a ^ 2 - b ^ 2 * lam
    have hd : d ≠ 0 := by
      have hAdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := A.det_ne_zero
      rw [hA, emb_det] at hAdet
      simpa [d] using hAdet
    refine ⟨A⁻¹, a / d, -b / d, ?_, ?_⟩
    · rw [hx]
      simp
    · have hmul : (A : Matrix (Fin 2) (Fin 2) K) * emb lam (a / d) (-b / d) = 1 := by
        rw [hA]
        rw [emb_mul]
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j
        · simp [emb]
          field_simp [d, hd]
          ring
        · have h : a * (-b / d) + b * (a / d) = 0 := by
            field_simp [d, hd]
            ring
          simp [emb, h, zero_mul]
        · have h : a * (-b / d) + b * (a / d) = 0 := by
            field_simp [d, hd]
            ring
          simp [emb, h]
        · simp [emb]
          field_simp [d, hd]
          ring
      exact by
        simpa using Matrix.inv_eq_right_inv (A := (A : Matrix (Fin 2) (Fin 2) K))
          (B := emb lam (a / d) (-b / d)) hmul

/-- Membership in the standard nonsplit torus, stated with its literal
matrix model so downstream modules need not unfold private helpers. -/
public theorem mem_pGammaL2NonsplitTorus_iff
    {K : Type u} [Field K] {lam : K} {x : PGL2 K} :
    x ∈ pGammaL2NonsplitTorus K lam ↔
      ∃ (A : GL (Fin 2) K) (a b : K),
        x = Matrix.ProjGenLinGroup.mk A ∧
          (A : Matrix (Fin 2) (Fin 2) K) = !![a, b * lam; b, a] := by
  rfl

/-- An element of the fixed subfield of an odd prime-order coefficient
automorphism is a square in `K` only if it is a square in the fixed
subfield.  Equivalently, a nonsquare in the fixed subfield remains a
nonsquare in `K`. -/
private theorem nonsquare_of_mem_fixedSubfield
    (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf sigma = p)
    (lam : K) (hlamFixed : lam ∈ FixedPoints.subfield (Subgroup.zpowers sigma) K)
    (hlamNS : ¬ IsSquare (⟨lam, hlamFixed⟩ :
      FixedPoints.subfield (Subgroup.zpowers sigma) K)) :
    ¬ IsSquare lam := by
  classical
  let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
  intro hlamK
  rcases hlamK with ⟨x, hx⟩
  have hx2 : x * x = lam := hx.symm
  let lamR : R := ⟨lam, hlamFixed⟩
  have haeval : Polynomial.aeval x (X ^ 2 - C lamR) = 0 := by
    calc
      Polynomial.aeval x (X ^ 2 - C lamR) = x ^ 2 - (lamR : K) := by
        simp [pow_two, Subfield.algebraMap_ofSubfield]
      _ = x ^ 2 - lam := by simp [lamR]
      _ = 0 := by rw [pow_two, ← hx2]; simp
  have hminpoly_dvd : minpoly R x ∣ X ^ 2 - C lamR := by
    exact minpoly.dvd R x haeval
  have hxint : IsIntegral R x := by
    refine ⟨X ^ 2 - C lamR, monic_X_pow_sub_C lamR (by norm_num), haeval⟩
  have hdeg : (minpoly R x).natDegree ≤ 2 := by
    calc
      (minpoly R x).natDegree ≤ (X ^ 2 - C lamR).natDegree :=
        natDegree_le_of_dvd hminpoly_dvd (X_pow_sub_C_ne_zero (by norm_num) lamR)
      _ = 2 := by rw [natDegree_X_pow_sub_C]
  have hfinrank_adjoin : Module.finrank R (IntermediateField.adjoin R {x}) = (minpoly R x).natDegree :=
    IntermediateField.adjoin.finrank hxint
  have hle2 : Module.finrank R (IntermediateField.adjoin R {x}) ≤ 2 := by
    rw [hfinrank_adjoin]
    exact hdeg
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  let : IsGaloisGroup (Subgroup.zpowers sigma) R K :=
    IsGaloisGroup.fixedPoints (Subgroup.zpowers sigma) K
  have hfinrankK : Module.finrank R K = p := by
    calc
      Module.finrank R K = Nat.card (Subgroup.zpowers sigma) := by
        symm
        dsimp [R]
        exact IsGaloisGroup.card_eq_finrank
          (Subgroup.zpowers sigma)
          (FixedPoints.subfield (Subgroup.zpowers sigma) K) K
      _ = orderOf sigma := Nat.card_zpowers sigma
      _ = p := hord
  have hdiv : Module.finrank R (IntermediateField.adjoin R {x}) ∣ p := by
    rw [← hfinrankK]
    have htower : Module.finrank R (IntermediateField.adjoin R {x}) *
          Module.finrank (IntermediateField.adjoin R {x}) K = Module.finrank R K :=
      Module.finrank_mul_finrank R (IntermediateField.adjoin R {x}) K
    rw [← htower]
    exact dvd_mul_right _ _
  have hpge3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := hp.two_le
    have hpne2 : p ≠ 2 := by
      intro hp2eq
      have hdiv2 : 2 ∣ p := by simp [hp2eq]
      exact hpodd.not_two_dvd_nat hdiv2
    omega
  have hlt : Module.finrank R (IntermediateField.adjoin R {x}) < p := by
    omega
  have hfin1 : Module.finrank R (IntermediateField.adjoin R {x}) = 1 := by
    exact ((Nat.dvd_prime hp).mp hdiv).resolve_right (ne_of_lt hlt)
  have hxbot : x ∈ (⊥ : IntermediateField R K) := by
    exact (IntermediateField.finrank_adjoin_simple_eq_one_iff
      (F := R) (E := K) (α := x)).mp hfin1
  rcases (IntermediateField.mem_bot.mp hxbot) with ⟨r, hr⟩
  have hlam_eq : lam = ((r * r : R) : K) := by
    calc
      lam = x * x := hx
      _ = (r : K) * (r : K) := by
        rw [← hr]
        simp [Subfield.algebraMap_ofSubfield]
      _ = ((r * r : R) : K) := by
        simp
  have hsq : IsSquare (⟨lam, hlamFixed⟩ : R) := by
    refine ⟨r, ?_⟩
    apply Subtype.ext
    change lam = ((r * r : R) : K)
    exact hlam_eq
  exact hlamNS hsq

/-- A subgroup of the standard nonsplit torus of `PGL₂(K)` that is
projectively centralized by a pure coefficient automorphism has order
dividing `|R| + 1`, where `R` is the fixed subfield of the automorphism.

No parity or coprimality hypothesis on `|A|` is needed: the nonsplit torus
has no sign ambiguity in its fixed points, so the bound includes the full
torus `2`-part. -/
public theorem pGammaL2_pureField_nonsplitTorus_fixedSubfield
    (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf sigma = p)
    (lam : K) (hlamFixed : lam ∈ FixedPoints.subfield (Subgroup.zpowers sigma) K)
    (hlamNS : ¬ IsSquare (⟨lam, hlamFixed⟩ :
      FixedPoints.subfield (Subgroup.zpowers sigma) K))
    (A : Subgroup (PGL2 K))
    (hAtorus : A ≤ pGammaL2NonsplitTorus K lam)
    (hcomm : ∀ x : PGL2 K, x ∈ A →
      Commute (SemidirectProduct.inr sigma : PGammaL2 K) (SemidirectProduct.inl x)) :
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    Nat.card A ∣ Nat.card R + 1 := by
  classical
  let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
  let U := pGammaL2NonsplitTorus K lam
  have hlamNS_K : ¬ IsSquare lam :=
    nonsquare_of_mem_fixedSubfield K sigma p hp hpodd hord lam hlamFixed hlamNS
  have hsigmaLam : sigma lam = lam := by
    have hfp : lam ∈ MulAction.fixedPoints (Subgroup.zpowers sigma) K := by
      change lam ∈ (FixedPoints.subfield (Subgroup.zpowers sigma) K : Set K)
      exact hlamFixed
    have h := (MulAction.mem_fixedPoints.mp hfp) ⟨sigma, Subgroup.mem_zpowers sigma⟩
    change sigma lam = lam
    simpa using h
  have hfixed : ∀ u : PGL2 K, u ∈ A → pgl2FieldAut K sigma u = u := by
    intro u hu
    have hmul := (hcomm u hu).eq
    rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def] at hmul
    simpa using congrArg SemidirectProduct.left hmul
  let Fix : Subgroup (PGL2 K) :=
    { carrier := {u : PGL2 K | u ∈ U ∧ pgl2FieldAut K sigma u = u}
      one_mem' := by
        refine ⟨U.one_mem, ?_⟩
        simp
      mul_mem' := by
        intro x y hx hy
        rcases hx with ⟨hxU, hxf⟩
        rcases hy with ⟨hyU, hyf⟩
        refine ⟨U.mul_mem hxU hyU, ?_⟩
        rw [map_mul, hxf, hyf]
      inv_mem' := by
        intro x hx
        rcases hx with ⟨hxU, hxf⟩
        refine ⟨U.inv_mem hxU, ?_⟩
        rw [map_inv, hxf] }
  have hsigmaA (A : GL (Fin 2) K) (a b : K)
      (hA : (A : Matrix (Fin 2) (Fin 2) K) = emb lam a b) :
      pgl2FieldAut K sigma (Matrix.ProjGenLinGroup.mk A) =
        Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom A) := by
    rw [pgl2FieldAut_apply]
    change pgl2RingEquiv sigma
        (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K)) A) =
      QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K))
        (Matrix.GeneralLinearGroup.map sigma.toRingHom A)
    rw [pgl2RingEquiv_mk]
  have hmapA (A : GL (Fin 2) K) (a b : K)
      (hA : (A : Matrix (Fin 2) (Fin 2) K) = emb lam a b) :
      (Matrix.GeneralLinearGroup.map sigma.toRingHom A :
          Matrix (Fin 2) (Fin 2) K) = emb lam (sigma a) (sigma b) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [emb, Matrix.GeneralLinearGroup.map, hA, hsigmaLam]
  have hdet_fixed (r : R) : (emb lam (r : K) 1).det ≠ 0 := by
    intro h
    apply hlamNS_K
    have hdet : (emb lam (r : K) 1).det = (r : K) ^ 2 - lam := by
      simpa [pow_two] using emb_det lam (r : K) 1
    rw [hdet] at h
    have hsq : (r : K) ^ 2 = lam := sub_eq_zero.mp h
    exact ⟨(r : K), by simpa [pow_two] using hsq.symm⟩
  let torusFixed (r : R) : PGL2 K :=
    Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.mkOfDetNeZero (emb lam (r : K) 1) (hdet_fixed r))
  have hfix_mem (r : R) : torusFixed r ∈ Fix := by
    refine ⟨?_, ?_⟩
    · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (emb lam (r : K) 1) (hdet_fixed r),
        (r : K), 1, rfl, rfl⟩
    · have hfixR : sigma (r : K) = (r : K) := by
        have hfp : (r : K) ∈ MulAction.fixedPoints (Subgroup.zpowers sigma) K := by
          change (r : K) ∈ (R : Set K)
          exact r.2
        have h := (MulAction.mem_fixedPoints.mp hfp) ⟨sigma, Subgroup.mem_zpowers sigma⟩
        change sigma (r : K) = (r : K)
        simpa using h
      change pgl2FieldAut K sigma
          (Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.mkOfDetNeZero (emb lam (r : K) 1) (hdet_fixed r))) =
        Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (emb lam (r : K) 1) (hdet_fixed r))
      rw [hsigmaA (Matrix.GeneralLinearGroup.mkOfDetNeZero (emb lam (r : K) 1) (hdet_fixed r))
        (r : K) 1 rfl]
      congr 1
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [hmapA (Matrix.GeneralLinearGroup.mkOfDetNeZero (emb lam (r : K) 1) (hdet_fixed r))
        (r : K) 1 rfl]
      fin_cases i <;> fin_cases j <;> simp [emb, hfixR]
  have hsurj : ∀ u : PGL2 K, u ∈ Fix → u = 1 ∨ ∃ r : R, u = torusFixed r := by
    intro u hu
    rcases hu with ⟨huU, hufix⟩
    rcases huU with ⟨A, a, b, huA, hAb⟩
    have hsigma : pgl2FieldAut K sigma (Matrix.ProjGenLinGroup.mk A) =
        Matrix.ProjGenLinGroup.mk A := by
      simpa [huA] using hufix
    have hsigma' : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom A) =
        Matrix.ProjGenLinGroup.mk A := by
      rwa [← hsigmaA A a b hAb]
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hsigma' with ⟨r0, hr0⟩
    have h00 := congrArg (fun B : GL (Fin 2) K =>
      ((B : Matrix (Fin 2) (Fin 2) K) 0 0)) hr0
    have h10 := congrArg (fun B : GL (Fin 2) K =>
      ((B : Matrix (Fin 2) (Fin 2) K) 1 0)) hr0
    have hsa : sigma a * (r0 : K) = a := by
      simpa [emb, hAb, hmapA A a b hAb, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using h00
    have hsb : sigma b * (r0 : K) = b := by
      simpa [emb, hAb, hmapA A a b hAb, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using h10
    by_cases hb : b = 0
    · left
      have ha : a ≠ 0 := by
        intro ha0
        apply A.det_ne_zero
        rw [hAb, emb_det, ha0, hb]
        simp
      have hscalar : A = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 a ha) := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [hAb, emb, hb, Matrix.GeneralLinearGroup.scalar]
      have h1 : Matrix.ProjGenLinGroup.mk A = 1 := by
        rw [hscalar]
        simp
      simpa [huA] using h1
    · right
      let r : K := a / b
      have hsa' : sigma a = a * (r0 : K)⁻¹ := by
        calc
          sigma a = (sigma a * (r0 : K)) * (r0 : K)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero r0), mul_one]
          _ = a * (r0 : K)⁻¹ := by rw [hsa]
      have hsb' : sigma b = b * (r0 : K)⁻¹ := by
        calc
          sigma b = (sigma b * (r0 : K)) * (r0 : K)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero r0), mul_one]
          _ = b * (r0 : K)⁻¹ := by rw [hsb]
      have hsigmaR : sigma r = r := by
        dsimp [r]
        calc
          sigma (a / b) = sigma a * (sigma b)⁻¹ := by
            rw [div_eq_mul_inv, map_mul, map_inv₀]
          _ = a * b⁻¹ := by
            rw [hsa', hsb']
            field_simp [hb, Units.ne_zero r0]
          _ = a / b := by rw [div_eq_mul_inv]
      have hmemR : r ∈ (R : Set K) := by
        change r ∈ MulAction.fixedPoints (Subgroup.zpowers sigma) K
        rw [MulAction.mem_fixedPoints]
        intro tau
        rcases Subgroup.mem_zpowers_iff.mp tau.2 with ⟨z, hz⟩
        have hfix : r ∈ MulAction.fixedBy K sigma := by
          change sigma r = r
          exact hsigmaR
        change (tau : K ≃+* K) r = r
        rw [← hz]
        exact MulAction.mem_fixedBy_zpow hfix z
      have hAeq : (A : Matrix (Fin 2) (Fin 2) K) = (b : K) • emb lam r 1 := by
        rw [hAb]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [emb, r, Matrix.smul_apply] <;> field_simp [hb]
      have hmk : Matrix.ProjGenLinGroup.mk A = torusFixed ⟨r, hmemR⟩ := by
        apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
        refine ⟨(Units.mk0 b hb)⁻¹, ?_⟩
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change ((A : Matrix (Fin 2) (Fin 2) K) *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 b hb)⁻¹ :
              Matrix (Fin 2) (Fin 2) K)) i j = (emb lam (r : K) 1) i j
        rw [hAeq]
        fin_cases i <;> fin_cases j <;>
          simp [emb, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply,
            Fin.sum_univ_two] <;> field_simp [hb]
      refine ⟨⟨r, hmemR⟩, ?_⟩
      calc
        u = Matrix.ProjGenLinGroup.mk A := huA
        _ = torusFixed ⟨r, hmemR⟩ := hmk
  have hinj : Function.Injective torusFixed := by
    intro r s hrs
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hrs with ⟨u, hu⟩
    have hu10 := congrArg (fun B : GL (Fin 2) K =>
      ((B : Matrix (Fin 2) (Fin 2) K) 1 0)) hu
    have hu00 := congrArg (fun B : GL (Fin 2) K =>
      ((B : Matrix (Fin 2) (Fin 2) K) 0 0)) hu
    have hu1 : (u : K) = 1 := by
      simpa [emb, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply,
        Fin.sum_univ_two] using hu10
    apply Subtype.ext
    simpa [emb, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply,
      Fin.sum_univ_two, hu1] using hu00
  have hne_one (r : R) : torusFixed r ≠ 1 := by
    intro h
    have hmk : Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (emb lam (r : K) 1) (hdet_fixed r)) = 1 := h
    rw [Matrix.ProjGenLinGroup.mk_eq_one] at hmk
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmk
    rcases hmk with ⟨u, hu⟩
    have hu10 := congrArg (fun B : GL (Fin 2) K =>
      ((B : Matrix (Fin 2) (Fin 2) K) 1 0)) hu
    have h10 : (1 : K) = 0 := by
      simpa [emb, Matrix.GeneralLinearGroup.scalar] using hu10.symm
    exact one_ne_zero h10
  let e : Sum.{u, u} (↥R) PUnit ≃ Fix :=
    { toFun := fun x => match x with
        | Sum.inl r => ⟨torusFixed r, hfix_mem r⟩
        | Sum.inr _ => ⟨1, Fix.one_mem⟩
      invFun := fun u =>
        if h : (u : PGL2 K) = 1 then Sum.inr PUnit.unit
        else Sum.inl (Classical.choose ((hsurj u u.2).resolve_left h))
      left_inv := by
        intro x
        cases x with
        | inl r =>
            simp [hne_one r]
            apply hinj
            symm
            exact Classical.choose_spec
              ((hsurj (torusFixed r) (hfix_mem r)).resolve_left (hne_one r))
        | inr _ =>
            simp
      right_inv := by
        intro u
        by_cases hu1 : (u : PGL2 K) = 1
        · simp [hu1]
          apply Subtype.ext
          exact hu1.symm
        · simp [hu1]
          apply Subtype.ext
          exact (Classical.choose_spec
            (Or.resolve_left (hsurj (u : PGL2 K) u.2) hu1)).symm }
  have hcardFix : Nat.card Fix = Nat.card R + 1 := by
    calc
      Nat.card Fix = Nat.card (R ⊕ PUnit) := (Nat.card_congr e).symm
      _ = Nat.card R + 1 := by simp
  have hAFix : A ≤ Fix := by
    intro u hu
    exact ⟨hAtorus hu, hfixed u hu⟩
  have hdvd : Nat.card A ∣ Nat.card Fix := Subgroup.card_dvd_of_le hAFix
  simpa [hcardFix] using hdvd

end CFSG.GorensteinWalter

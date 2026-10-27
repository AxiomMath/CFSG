module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2InnerNonsplitTorusFieldFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2ConcreteNonsplitTorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The nonsplit-half fixed-field divisibility for the semilinear conjugate

This is the nonsplit half of the `hU0fixed` transport used by the
equation-(4) PSL₂ branch, mirroring the split half
`pGammaL2_splitTorus_semilinearConjugate_fixedSubfield`.  Let
`sigma : K ≃+* K` be an odd prime-order coefficient automorphism,
`z : PGL2 K` a projective matrix, `lam` a nonsquare of `K` fixed by
`sigma`, and `A` a subgroup of the concrete nonsplit torus
`U := pgl2ConcreteNonsplitTorus K lam` whose image lies in the derived
`PSL₂` layer.  Assume that for every `x ∈ A` the semilinear conjugate
`z · σ̃(x) · z⁻¹` equals `x`, where `σ̃ := pgl2FieldAut K sigma` applies
`sigma` to the matrix entries.

Then `|A| ∣ (|Fix σ| + 1)/2`.  The proof splits on whether `σ̃` fixes `A`
pointwise:

* diagonal case: `A` embeds into the `σ̃`-fixed part of the torus, which
  has `|R| + 1` elements (`R := Fix σ`); intersecting with the derived
  `PSL₂` layer halves this, so
  `pGammaL2_pureField_innerNonsplitTorus_fixedSubfield` gives the half
  divisibility directly;
* moved case: the matrix conjugation equation
  `M · σ(N) · M⁻¹ = μ · N` for the lift `x = mk N`, `N = !![a, b·lam; b, a]`
  forces, by traces and determinants (with `2 ≠ 0`), the sign-flip
  `σ(a)·b = −σ(b)·a`, i.e. `σ̃(x) = x⁻¹`; an odd-order automorphism cannot
  invert an element (`mulAut_inverted_sq_eq_one` collapses inversion to
  `x² = 1`), so `x = x⁻¹`, contradicting that `x` was moved.  Hence the
  moved case is empty and no parity hypothesis is needed.

Note that the endpoint is `(|R| + 1)/2`, not `(|R| − 1)/2`: the nonsplit
torus has `|K| + 1` elements and its `sigma`-fixed part `|R| + 1`, while the
`(±)`-split that appears in the split half comes from the split torus
`|K| − 1` / fixed units `|R| − 1`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

private lemma two_ne_zero_of_odd_card (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  intro h2
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd_char : ringChar K ∣ 2 := (CharP.cast_eq_zero_iff K (ringChar K) 2).mp h2
  have hchar2 : ringChar K = 2 := by
    rcases hdvd_char with ⟨c, hc⟩
    cases c with
    | zero => norm_num at hc
    | succ c =>
        cases c with
        | zero => omega
        | succ c =>
            exfalso
            have hrc_pos : 0 < ringChar K := by
              by_contra h
              have hz : ringChar K = 0 := by omega
              rw [hz] at hc
              norm_num at hc
            have hrc_le : ringChar K ≤ 1 := by nlinarith
            have hrc1 : ringChar K = 1 := by omega
            have hsub : Subsingleton K := (ringChar.ringChar_eq_one (R := K)).mp hrc1
            exact not_subsingleton K hsub
  have hdvd_card : 2 ∣ Fintype.card K :=
    (prime_dvd_char_iff_dvd_card (R := K) (p := 2)).mp (by simpa [hchar2])
  have hprime_dvd : (2 : ℕ) ∣ Nat.card K := by
    simpa [Nat.card_eq_fintype_card] using hdvd_card
  exact hodd.not_two_dvd_nat hprime_dvd

/-- A coefficient automorphism acts on the projective image of a matrix by
mapping the matrix entries. -/
private lemma pgl2FieldAut_mk (K : Type u) [Field K]
    (sigma : K ≃+* K) (A : GL (Fin 2) K) :
    pgl2FieldAut K sigma (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom A) := by
  rw [pgl2FieldAut_apply]
  change pgl2RingEquiv sigma (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K)) A) =
    QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K))
      (Matrix.GeneralLinearGroup.map sigma.toRingHom A)
  rw [pgl2RingEquiv_mk]

/-- The inverse of a general-linear matrix, as a matrix, cancels the matrix
itself. -/
private lemma inv_mul_self_matrix (K : Type u) [Field K]
    (M : GL (Fin 2) K) :
    (M⁻¹ : Matrix (Fin 2) (Fin 2) K) * (M : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp [Matrix.GeneralLinearGroup.coe_inv]

/-- A nonzero quotient `sigma x / x` is again nonzero. -/
private lemma sigma_div_ne_zero (K : Type u) [Field K]
    (sigma : K ≃+* K) {x : K} (hx : x ≠ 0) : sigma x / x ≠ 0 := by
  intro h
  apply hx
  have h0 : sigma x = 0 := by
    have h' : sigma x * x⁻¹ = 0 := by simpa [div_eq_mul_inv] using h
    exact (mul_eq_zero.mp h').resolve_right (inv_ne_zero hx)
  exact sigma.injective (by simpa [h0] using (map_zero sigma))

/-- The projective conjugation equation `z · σ̃(mk N) · z⁻¹ = mk N` lifts to
a matrix-level similarity `M · σ(N) · M⁻¹ = μ • N`. -/
private lemma semilinear_conj_similarity (K : Type u) [Field K]
    (sigma : K ≃+* K) (M N : GL (Fin 2) K)
    (h : Matrix.ProjGenLinGroup.mk M *
          Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom N) *
            (Matrix.ProjGenLinGroup.mk M)⁻¹ =
          Matrix.ProjGenLinGroup.mk N) :
    ∃ mu : Kˣ,
      (M : Matrix (Fin 2) (Fin 2) K) *
          (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
            (M⁻¹ : Matrix (Fin 2) (Fin 2) K) =
        (mu : K) • (N : Matrix (Fin 2) (Fin 2) K) := by
  have hinv : (Matrix.ProjGenLinGroup.mk M)⁻¹ =
      Matrix.ProjGenLinGroup.mk (M⁻¹) := by
    exact (map_inv Matrix.ProjGenLinGroup.mk M).symm
  rw [hinv, ← map_mul, ← map_mul] at h
  rcases (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mp h with ⟨u, hu⟩
  let S : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) u
  have huM : ((M * (Matrix.GeneralLinearGroup.map sigma.toRingHom N) * M⁻¹) * S) * M =
      N * M := by
    exact congrArg (fun X : GL (Fin 2) K => X * M) hu
  have hSM : (S : Matrix (Fin 2) (Fin 2) K) = (u : K) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S, Matrix.GeneralLinearGroup.scalar,
      Matrix.smul_apply, one_apply, smul_eq_mul]
  have hstep : (M * (Matrix.GeneralLinearGroup.map sigma.toRingHom N)) * S = N * M := by
    calc
      (M * (Matrix.GeneralLinearGroup.map sigma.toRingHom N)) * S =
          (M * (Matrix.GeneralLinearGroup.map sigma.toRingHom N)) * (M⁻¹ * M) * S := by group
      _ = (M * (Matrix.GeneralLinearGroup.map sigma.toRingHom N) * M⁻¹) * (M * S) := by group
      _ = (M * (Matrix.GeneralLinearGroup.map sigma.toRingHom N) * M⁻¹) * (S * M) := by
        congr 1
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [S, Matrix.GeneralLinearGroup.scalar,
          Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, one_apply,
          mul_comm, mul_left_comm, mul_assoc]
      _ = ((M * (Matrix.GeneralLinearGroup.map sigma.toRingHom N) * M⁻¹) * S) * M := by group
      _ = N * M := huM
  have hprod : (M : Matrix (Fin 2) (Fin 2) K) *
      (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
        (S : Matrix (Fin 2) (Fin 2) K) =
      (N : Matrix (Fin 2) (Fin 2) K) * (M : Matrix (Fin 2) (Fin 2) K) := by
    have hstep' := congrArg
      (fun X : GL (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hstep
    simpa [map_mul] using hstep'
  rw [hSM] at hprod
  rw [Matrix.mul_smul, Matrix.mul_one] at hprod
  refine ⟨u⁻¹, ?_⟩
  have h1 : (u : K) • ((M : Matrix (Fin 2) (Fin 2) K) *
      (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
        (M⁻¹ : Matrix (Fin 2) (Fin 2) K)) = (N : Matrix (Fin 2) (Fin 2) K) := by
    calc
      (u : K) • ((M : Matrix (Fin 2) (Fin 2) K) *
          (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
            (M⁻¹ : Matrix (Fin 2) (Fin 2) K))
          = ((u : K) • ((M : Matrix (Fin 2) (Fin 2) K) *
              (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K))) *
              (M⁻¹ : Matrix (Fin 2) (Fin 2) K) := by
            rw [Matrix.smul_mul]
      _ = ((N : Matrix (Fin 2) (Fin 2) K) * (M : Matrix (Fin 2) (Fin 2) K)) *
              (M⁻¹ : Matrix (Fin 2) (Fin 2) K) := by rw [hprod]
      _ = (N : Matrix (Fin 2) (Fin 2) K) := by
            simp [Matrix.mul_assoc, inv_mul_self_matrix]
  have h1' : (u⁻¹ : K) • ((u : K) • ((M : Matrix (Fin 2) (Fin 2) K) *
      (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
        (M⁻¹ : Matrix (Fin 2) (Fin 2) K))) =
      (u⁻¹ : K) • (N : Matrix (Fin 2) (Fin 2) K) := by
    exact congrArg (fun X : Matrix (Fin 2) (Fin 2) K => (u⁻¹ : K) • X) h1
  have hinv1 : (u⁻¹ : K) * (u : K) = 1 := by
    simpa [mul_comm] using (Units.val_inv u)
  simpa [smul_smul, hinv1] using h1'

/-- A pure coefficient automorphism commuting with an element of the
nonsplit torus: from `σ̃(x) = x` the semilinear element `(1, σ)` commutes
with the projective class `x`. -/
private lemma pGammaL2_sigma_commute (K : Type u) [Field K]
    (sigma : K ≃+* K) (x : PGL2 K)
    (hfix : pgl2FieldAut K sigma x = x) :
    Commute (SemidirectProduct.inr sigma : PGammaL2 K)
      (SemidirectProduct.inl x) := by
  change SemidirectProduct.inr sigma *
      SemidirectProduct.inl x =
    SemidirectProduct.inl x * (SemidirectProduct.inr sigma : PGammaL2 K)
  rw [SemidirectProduct.mul_def (SemidirectProduct.inr sigma)
      (SemidirectProduct.inl x),
    SemidirectProduct.mul_def (SemidirectProduct.inl x)
      (SemidirectProduct.inr sigma)]
  apply SemidirectProduct.ext
  · calc
      (1 : PGL2 K) * pgl2FieldAut K sigma x = pgl2FieldAut K sigma x := by simp
      _ = x := hfix
      _ = x * (pgl2FieldAut K (1 : K ≃+* K)) 1 := by simp
  · simp

/-- An odd-order automorphism collapses inversion: if `f` has odd order `p`
and inverts `x`, then `x` is an involution. -/
public theorem mulAut_inverted_sq_eq_one
    {G : Type u} [Group G]
    (f : G ≃* G) (p : ℕ) (hpodd : Odd p) (hfpow : f ^ p = 1)
    (x : G) (hinv : f x = x⁻¹) :
    x * x = 1 := by
  have hf2 : (f ^ 2) x = x := by
    calc
      (f ^ 2) x = f (f x) := by rfl
      _ = f x⁻¹ := by rw [hinv]
      _ = (f x)⁻¹ := map_inv f x
      _ = (x⁻¹)⁻¹ := by rw [hinv]
      _ = x := by simp
  have h2pow (k : ℕ) : ((f ^ 2) ^ k) x = x ∧ ((f ^ 2) ^ k) (x⁻¹) = x⁻¹ := by
    induction k with
    | zero => simp
    | succ k ih =>
        constructor
        · calc
            ((f ^ 2) ^ (k + 1)) x = (f ^ 2) (((f ^ 2) ^ k) x) := by
              rw [pow_succ']
              simp
            _ = (f ^ 2) x := by rw [ih.1]
            _ = x := hf2
        · calc
            ((f ^ 2) ^ (k + 1)) (x⁻¹) = (f ^ 2) (((f ^ 2) ^ k) (x⁻¹)) := by
              rw [pow_succ']
              simp
            _ = (f ^ 2) (x⁻¹) := by rw [ih.2]
            _ = x⁻¹ := by
              calc
                ((f ^ 2) (x⁻¹)) = f (f (x⁻¹)) := by rfl
                _ = f ((f x)⁻¹) := by rw [map_inv]
                _ = (f (f x))⁻¹ := map_inv f (f x)
                _ = ((f ^ 2) x)⁻¹ := by rfl
                _ = x⁻¹ := by rw [hf2]
  rcases hpodd with ⟨m, hm⟩
  have hfp : (f ^ p) x = x⁻¹ := by
    calc
      (f ^ p) x = (f ^ (2 * m + 1)) x := by rw [hm]
      _ = (f ^ (2 * m)) (f x) := by
        rw [pow_succ]
        simp
      _ = (f ^ (2 * m)) (x⁻¹) := by rw [hinv]
      _ = ((f ^ 2) ^ m) (x⁻¹) := by rw [← pow_mul]
      _ = x⁻¹ := (h2pow m).2
  have hfpid : (f ^ p) x = x := by
    rw [hfpow]
    simp
  have hxx : x = x⁻¹ := by
    calc
      x = (f ^ p) x := hfpid.symm
      _ = x⁻¹ := hfp
  calc
    x * x = x * x⁻¹ := by rw [← hxx]
    _ = 1 := by exact mul_inv_cancel x

/-- A moved nonsplit-torus element under a semilinear conjugate is inverted:
the matrix equation `M · σ(N) · M⁻¹ = μ • N` for the lift `x = mk N`,
`N = !![a, b·lam; b, a]`, forces by traces and determinants the sign-flip
`σ(a)·b = −σ(b)·a`, i.e. `σ̃(x) = x⁻¹`. -/
private lemma moved_nonsplitTorus_element_inverted
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (sigma : K ≃+* K) (lam : K) (hlamσ : sigma lam = lam) (hlam0 : lam ≠ 0)
    (z : PGL2 K) (x : PGL2 K)
    (hxU : x ∈ pgl2ConcreteNonsplitTorus K lam)
    (hconj : z * pgl2FieldAut K sigma x * z⁻¹ = x)
    (hmoved : pgl2FieldAut K sigma x ≠ x) :
    pgl2FieldAut K sigma x = x⁻¹ := by
  classical
  have htwo : (2 : K) ≠ 0 := two_ne_zero_of_odd_card K (by
    rcases hK with ⟨q, n, hq, hqodd, hn, hKcard⟩
    rw [hKcard]
    exact hqodd.pow)
  have hxU' : x ∈ pGammaL2NonsplitTorus K lam := by
    rw [← pgl2ConcreteNonsplitTorus_eq_pGammaL2NonsplitTorus K lam]
    exact hxU
  rcases (mem_pGammaL2NonsplitTorus_iff.mp hxU') with ⟨N, a, b, hx, hN⟩
  rcases Matrix.ProjGenLinGroup.mk_surjective z with ⟨M, rfl⟩

  have hMk : pgl2FieldAut K sigma (Matrix.ProjGenLinGroup.mk N) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom N) :=
    pgl2FieldAut_mk K sigma N
  have hconjMk : Matrix.ProjGenLinGroup.mk M *
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom N) *
        (Matrix.ProjGenLinGroup.mk M)⁻¹ = Matrix.ProjGenLinGroup.mk N := by
    simpa [hx, hMk] using hconj
  rcases semilinear_conj_similarity K sigma M N hconjMk with ⟨mu, hmu⟩
  have hσN : (Matrix.GeneralLinearGroup.map sigma.toRingHom N :
      Matrix (Fin 2) (Fin 2) K) = !![sigma a, sigma b * lam; sigma b, sigma a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, hN, hlamσ]
  have hb_ne : b ≠ 0 := by
    intro hb0
    apply hmoved
    rw [hx]
    have hNscalar : (N : Matrix (Fin 2) (Fin 2) K) = (a : K) • 1 := by
      rw [hN, hb0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, one_apply, smul_eq_mul]
    have ha_ne0 : a ≠ 0 := by
      intro ha0
      apply N.det_ne_zero
      rw [hN, hb0, ha0]
      simp
    have hNscalarGL : N = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 a ha_ne0) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.scalar, hNscalar, Matrix.smul_apply,
          one_apply, smul_eq_mul]
    have hσNscalar : (Matrix.GeneralLinearGroup.map sigma.toRingHom N :
        Matrix (Fin 2) (Fin 2) K) = (sigma a : K) • 1 := by
      rw [hσN, hb0]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.smul_apply, one_apply, smul_eq_mul]
    have hσa_ne : sigma a ≠ 0 := by
      intro hsa
      exact ha_ne0 (sigma.injective (by simpa [hsa] using (map_zero sigma)))
    have hσNscalarGL : Matrix.GeneralLinearGroup.map sigma.toRingHom N =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (sigma a) hσa_ne) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change ((Matrix.GeneralLinearGroup.map sigma.toRingHom N :
        Matrix (Fin 2) (Fin 2) K) i j) =
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (sigma a) hσa_ne) :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
      rw [hσN]
      fin_cases i <;> fin_cases j <;>
        simp [hb0, Matrix.GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply,
          smul_eq_mul]
    have h1 : Matrix.ProjGenLinGroup.mk N = 1 := by
      rw [hNscalarGL]
      simp
    have h2 : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom N) = 1 := by
      rw [hσNscalarGL]
      simp
    rw [hMk, h1, h2]
  have ha_ne : a ≠ 0 := by
    intro ha0
    apply hmoved
    rw [hx, hMk]
    have hσb_ne : sigma b ≠ 0 := by
      intro hsb
      exact hb_ne (sigma.injective (by simpa [hsb] using (map_zero sigma)))
    apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨Units.mk0 (b / sigma b) (div_ne_zero hb_ne hσb_ne), ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change ((Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (b / sigma b) (div_ne_zero hb_ne hσb_ne)) :
          Matrix (Fin 2) (Fin 2) K)) i j =
      (N : Matrix (Fin 2) (Fin 2) K) i j
    rw [hσN, hN]
    fin_cases i <;> fin_cases j <;>
      simp [ha0, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        div_eq_mul_inv] <;> field_simp [hb_ne, hσb_ne]
  have htr := congrArg Matrix.trace hmu
  have htrL : Matrix.trace ((M : Matrix (Fin 2) (Fin 2) K) *
      (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
        (M⁻¹ : Matrix (Fin 2) (Fin 2) K)) = 2 * sigma a := by
    calc
      Matrix.trace ((M : Matrix (Fin 2) (Fin 2) K) *
          (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
            (M⁻¹ : Matrix (Fin 2) (Fin 2) K))
          = Matrix.trace ((M⁻¹ : Matrix (Fin 2) (Fin 2) K) *
              ((M : Matrix (Fin 2) (Fin 2) K) *
                (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K))) := by
            exact Matrix.trace_mul_comm
              ((M : Matrix (Fin 2) (Fin 2) K) *
                (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K))
              (M⁻¹ : Matrix (Fin 2) (Fin 2) K)
      _ = Matrix.trace (Matrix.GeneralLinearGroup.map sigma.toRingHom N :
          Matrix (Fin 2) (Fin 2) K) := by
            simp
      _ = 2 * sigma a := by
            rw [hσN]
            simp
            ring
  have htrR : Matrix.trace ((mu : K) • (N : Matrix (Fin 2) (Fin 2) K)) =
      (mu : K) * (2 * a) := by
    rw [Matrix.trace_smul]
    simp [hN]
    ring
  have htr' : 2 * sigma a = (mu : K) * (2 * a) := by
    calc
      2 * sigma a = Matrix.trace ((M : Matrix (Fin 2) (Fin 2) K) *
          (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
            (M⁻¹ : Matrix (Fin 2) (Fin 2) K)) := htrL.symm
      _ = Matrix.trace ((mu : K) • (N : Matrix (Fin 2) (Fin 2) K)) := htr
      _ = (mu : K) * (2 * a) := htrR
  have hσa : sigma a = (mu : K) * a := by
    apply mul_left_cancel₀ htwo
    calc
      (2 : K) * sigma a = (mu : K) * (2 * a) := htr'
      _ = 2 * ((mu : K) * a) := by ring
  have hdet := congrArg Matrix.det hmu
  have hdetL : Matrix.det ((M : Matrix (Fin 2) (Fin 2) K) *
      (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
        (M⁻¹ : Matrix (Fin 2) (Fin 2) K)) = sigma a ^ 2 - sigma b ^ 2 * lam := by
    calc
      Matrix.det ((M : Matrix (Fin 2) (Fin 2) K) *
          (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
            (M⁻¹ : Matrix (Fin 2) (Fin 2) K))
          = Matrix.det ((M⁻¹ : Matrix (Fin 2) (Fin 2) K) *
              ((M : Matrix (Fin 2) (Fin 2) K) *
                (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K))) := by
            exact Matrix.det_mul_comm
              ((M : Matrix (Fin 2) (Fin 2) K) *
                (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K))
              (M⁻¹ : Matrix (Fin 2) (Fin 2) K)
      _ = Matrix.det (Matrix.GeneralLinearGroup.map sigma.toRingHom N :
          Matrix (Fin 2) (Fin 2) K) := by
            simp
      _ = sigma a ^ 2 - sigma b ^ 2 * lam := by
            rw [hσN]
            simp [Matrix.det_fin_two]
            ring
  have hdetR : Matrix.det ((mu : K) • (N : Matrix (Fin 2) (Fin 2) K)) =
      (mu : K) ^ 2 * (a ^ 2 - b ^ 2 * lam) := by
    rw [Matrix.det_smul, hN]
    simp [Matrix.det_fin_two]
    ring
  have hdet' : sigma a ^ 2 - sigma b ^ 2 * lam =
      (mu : K) ^ 2 * (a ^ 2 - b ^ 2 * lam) := by
    calc
      sigma a ^ 2 - sigma b ^ 2 * lam =
          Matrix.det ((M : Matrix (Fin 2) (Fin 2) K) *
            (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
              (M⁻¹ : Matrix (Fin 2) (Fin 2) K)) := hdetL.symm
      _ = Matrix.det ((mu : K) • (N : Matrix (Fin 2) (Fin 2) K)) := hdet
      _ = (mu : K) ^ 2 * (a ^ 2 - b ^ 2 * lam) := hdetR
  have hσb : sigma b ^ 2 = (mu : K) ^ 2 * b ^ 2 := by
    have h' : sigma b ^ 2 * lam = (mu : K) ^ 2 * b ^ 2 * lam := by
      calc
        sigma b ^ 2 * lam = sigma a ^ 2 - (sigma a ^ 2 - sigma b ^ 2 * lam) := by ring
        _ = sigma a ^ 2 - (mu : K) ^ 2 * (a ^ 2 - b ^ 2 * lam) := by rw [hdet']
        _ = (mu : K) ^ 2 * b ^ 2 * lam := by rw [hσa]; ring
    exact mul_left_cancel₀ hlam0 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h')
  have hsq : (sigma a * b) ^ 2 = (sigma b * a) ^ 2 := by
    calc
      (sigma a * b) ^ 2 = (sigma a) ^ 2 * b ^ 2 := by ring
      _ = (mu : K) ^ 2 * (a ^ 2 * b ^ 2) := by rw [hσa]; ring
      _ = (sigma b) ^ 2 * a ^ 2 := by rw [hσb]; ring
      _ = (sigma b * a) ^ 2 := by ring
  have hne : sigma a * b ≠ sigma b * a := by
    intro h
    apply hmoved
    rw [hx, hMk]
    have hσa_ne : sigma a ≠ 0 := by
      intro hsa
      exact ha_ne (sigma.injective (by simpa [hsa] using (map_zero sigma)))
    apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨Units.mk0 (a / sigma a) (div_ne_zero ha_ne hσa_ne), ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change ((Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (a / sigma a) (div_ne_zero ha_ne hσa_ne)) :
          Matrix (Fin 2) (Fin 2) K)) i j =
      (N : Matrix (Fin 2) (Fin 2) K) i j
    rw [hσN, hN]
    fin_cases i <;> fin_cases j
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        div_eq_mul_inv] <;> field_simp [ha_ne, hσa_ne] <;>
          (try rw [h]) <;> (try rw [h.symm]) <;> ring
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        div_eq_mul_inv] <;> field_simp [ha_ne, hσa_ne] <;>
          (try rw [h]) <;> (try rw [h.symm]) <;> ring
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        div_eq_mul_inv] <;> field_simp [ha_ne, hσa_ne] <;>
          (try rw [h]) <;> (try rw [h.symm]) <;> ring
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        div_eq_mul_inv] <;> field_simp [ha_ne, hσa_ne] <;>
          (try rw [h]) <;> (try rw [h.symm]) <;> ring
  have hneg : sigma a * b = -(sigma b * a) := by
    have hfac : (sigma a * b - sigma b * a) * (sigma a * b + sigma b * a) = 0 := by
      calc
        (sigma a * b - sigma b * a) * (sigma a * b + sigma b * a) =
            (sigma a * b) ^ 2 - (sigma b * a) ^ 2 := by ring
        _ = 0 := by rw [hsq]; ring
    have hsub_ne : sigma a * b - sigma b * a ≠ 0 := sub_ne_zero.mpr hne
    have hsum0 : sigma a * b + sigma b * a = 0 :=
      (mul_eq_zero.mp hfac).resolve_left hsub_ne
    exact eq_neg_of_add_eq_zero_left hsum0
  have hinverted : Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map sigma.toRingHom N) =
      (Matrix.ProjGenLinGroup.mk N)⁻¹ := by
    have hprod : (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
        (N : Matrix (Fin 2) (Fin 2) K) = (sigma a * a + sigma b * lam * b) • 1 := by
      rw [hσN, hN]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hneg] <;>
          try ring <;>
          try linear_combination lam * hneg
    have hc_ne : sigma a * a + sigma b * lam * b ≠ 0 := by
      intro hc
      have hd0 : Matrix.det ((Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
          (N : Matrix (Fin 2) (Fin 2) K)) = 0 := by
        rw [hprod, hc]
        simp
      have hd_ne : Matrix.det ((Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
          (N : Matrix (Fin 2) (Fin 2) K)) ≠ 0 := by
        rw [Matrix.det_mul]
        exact mul_ne_zero (Matrix.GeneralLinearGroup.map sigma.toRingHom N).det_ne_zero N.det_ne_zero
      exact hd_ne hd0
    have hcommMat : (N : Matrix (Fin 2) (Fin 2) K) *
        (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) =
      (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) *
        (N : Matrix (Fin 2) (Fin 2) K) := by
      rw [hN, hσN]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have hprod' : (N : Matrix (Fin 2) (Fin 2) K) *
        (Matrix.GeneralLinearGroup.map sigma.toRingHom N : Matrix (Fin 2) (Fin 2) K) =
      (sigma a * a + sigma b * lam * b) • 1 := hcommMat.trans hprod
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul]
    apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 (sigma a * a + sigma b * lam * b) hc_ne, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hp := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A i j) hprod'
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply,
        smul_eq_mul] using hp.symm
  simpa [hx, hMk] using hinverted

/-- The matrix conjugation dichotomy for the semilinear conjugate on the
concrete nonsplit torus: for an element `x ∈ U` with
`z · σ̃(x) · z⁻¹ = x`, the parameter of `x` is either fixed by `sigma`
(`σ̃(x) = x`) or inverted (`σ̃(x) = x⁻¹`). -/
public theorem pGammaL2_nonsplitTorus_semilinearConjugate_dichotomy
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (sigma : K ≃+* K) (lam : K) (hlamσ : sigma lam = lam) (hlam0 : lam ≠ 0)
    (z : PGL2 K) (x : PGL2 K)
    (hxU : x ∈ pgl2ConcreteNonsplitTorus K lam)
    (hconj : z * pgl2FieldAut K sigma x * z⁻¹ = x) :
    pgl2FieldAut K sigma x = x ∨ pgl2FieldAut K sigma x = x⁻¹ := by
  by_cases hdiag : pgl2FieldAut K sigma x = x
  · exact Or.inl hdiag
  · exact Or.inr (moved_nonsplitTorus_element_inverted hK sigma lam hlamσ hlam0 z x
      hxU hconj hdiag)

set_option maxHeartbeats 8000000 in
/-- The nonsplit half of the `hU0fixed` transport: a subgroup `A` of the
concrete nonsplit torus whose image lies in the derived `PSL₂` layer and
whose elements are semilinearly conjugated by `(z, σ)` has order dividing
`(|Fix σ| + 1)/2`. -/
public theorem pGammaL2_nonsplitTorus_semilinearConjugate_fixedSubfield
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (sigma : K ≃+* K) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf sigma = p)
    (lam : K)
    (hlamFixed : lam ∈ FixedPoints.subfield (Subgroup.zpowers sigma) K)
    (hlamNS : ¬ IsSquare (⟨lam, hlamFixed⟩ :
      FixedPoints.subfield (Subgroup.zpowers sigma) K))
    (z : PGL2 K)
    (A : Subgroup (PGL2 K))
    (hAtorus : A ≤ pgl2ConcreteNonsplitTorus K lam)
    (hAinner : A ≤ commutator (PGL2 K))
    (hconj : ∀ x : PGL2 K, x ∈ A →
      z * pgl2FieldAut K sigma x * z⁻¹ = x) :
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    Nat.card A ∣ (Nat.card R + 1) / 2 := by
  classical
  by_cases hdiag : ∀ x : PGL2 K, x ∈ A → pgl2FieldAut K sigma x = x
  · -- DIAGONAL CASE: σ̃ fixes A pointwise
    have hAtorus' : A ≤ pGammaL2NonsplitTorus K lam := by
      simpa only [pgl2ConcreteNonsplitTorus_eq_pGammaL2NonsplitTorus] using hAtorus
    have hcommA : ∀ x : PGL2 K, x ∈ A →
        Commute (SemidirectProduct.inr sigma : PGammaL2 K)
          (SemidirectProduct.inl x) := by
      intro x hx
      exact pGammaL2_sigma_commute K sigma x (hdiag x hx)
    exact pGammaL2_pureField_innerNonsplitTorus_fixedSubfield
      K hK hcard sigma p hp hpodd hord lam hlamFixed hlamNS
      A hAtorus' hAinner hcommA
  · -- MOVED CASE: a moved element would be inverted, and odd prime order
    -- collapses inversion, contradicting that it was moved; hence empty
    have hnot' : ∃ x : PGL2 K, x ∈ A ∧ pgl2FieldAut K sigma x ≠ x := by
      by_contra h
      apply hdiag
      intro x hx
      by_contra hne
      apply h
      exact ⟨x, hx, hne⟩
    rcases hnot' with ⟨x₀, hx₀A, hx₀moved⟩
    have hlam0 : lam ≠ 0 := by
      intro hlam0
      apply hlamNS
      subst hlam0
      refine ⟨0, ?_⟩
      apply Subtype.ext
      simp
    have hlamσ : sigma lam = lam := by
      have hfp : lam ∈ MulAction.fixedPoints (Subgroup.zpowers sigma) K := by
        change lam ∈ (FixedPoints.subfield (Subgroup.zpowers sigma) K : Set K)
        exact hlamFixed
      have h := (MulAction.mem_fixedPoints.mp hfp) ⟨sigma, Subgroup.mem_zpowers sigma⟩
      change sigma lam = lam
      simpa using h
    have hinv : pgl2FieldAut K sigma x₀ = x₀⁻¹ :=
      moved_nonsplitTorus_element_inverted hK sigma lam hlamσ hlam0 z x₀
        (hAtorus hx₀A) (hconj x₀ hx₀A) hx₀moved
    have hsq : x₀ * x₀ = 1 :=
      mulAut_inverted_sq_eq_one (pgl2FieldAut K sigma) p hpodd (by
        rw [← map_pow]
        have hσp : sigma ^ p = 1 := by
          rw [← hord]
          exact pow_orderOf_eq_one sigma
        rw [hσp]
        simp) x₀ hinv
    have hxx : x₀ = x₀⁻¹ := by
      calc
        x₀ = x₀ * 1 := by simp
        _ = x₀ * (x₀ * x₀⁻¹) := by simp
        _ = (x₀ * x₀) * x₀⁻¹ := by group
        _ = 1 * x₀⁻¹ := by rw [hsq]
        _ = x₀⁻¹ := by simp
    exact False.elim (hx₀moved (by simpa [hinv] using hxx.symm))

end CFSG.GorensteinWalter

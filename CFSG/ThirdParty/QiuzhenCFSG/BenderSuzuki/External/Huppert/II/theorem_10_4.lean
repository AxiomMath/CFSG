module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.Algebra.Ring.Action.End
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.10.4

This file records the three-dimensional change-of-basis consequence used in
Huppert II.10.12 and II.10.13.
-/

namespace CFSG.BenderSuzuki
namespace External

open _root_.CFSG.BenderSuzuki.MatrixGroups
open scoped Matrix

universe u

private theorem hermitian_fixedField_finrank_two
    {K : Type u} [Field K] [Finite K] {n : ℕ}
    (J : HermitianForm n K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    Module.finrank (FixedBy.subfield K J.conj) K = 2 := by
  let k0 := FixedBy.subfield K J.conj
  have hset : (k0 : Set K) = {x : K | J.conj x = x} := by
    ext x
    rfl
  have hk0card : Nat.card k0 = q := by
    have hc := Nat.card_congr (Set.equivOfEq hset)
    simpa [k0] using hc.trans hfixed_card
  have hq : 1 < q := by
    rw [← hk0card]
    exact Finite.one_lt_card
  have hcard := Module.natCard_eq_pow_finrank (K := k0) (V := K)
  have hpows : q ^ Module.finrank k0 K = q ^ 2 := by
    calc
      q ^ Module.finrank k0 K = Nat.card k0 ^ Module.finrank k0 K := by
        rw [hk0card]
      _ = Nat.card K := hcard.symm
      _ = q ^ 2 := hKcard
  exact (pow_right_inj₀ (Nat.zero_lt_of_lt hq) (ne_of_gt hq)).mp hpows

private theorem card_fixedBy_subfield
    {K : Type u} [Field K] [Finite K] {n : ℕ}
    (J : HermitianForm n K) :
    Nat.card (FixedBy.subfield K J.conj) = Nat.card {x : K // J.conj x = x} := by
  let k0 := FixedBy.subfield K J.conj
  have hset : (k0 : Set K) = {x : K | J.conj x = x} := by
    ext x
    rfl
  change Nat.card k0 = Nat.card {x : K // J.conj x = x}
  exact Nat.card_congr (Set.equivOfEq hset)

/-- The fixed field of a quadratic finite-field Hermitian involution has
extension degree two. -/
public theorem huppert_II_10_4_fixedField_finrank_two
    {K : Type u} [Field K] [Finite K] {n : ℕ}
    (J : HermitianForm n K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    Module.finrank (FixedBy.subfield K J.conj) K = 2 :=
  by exact hermitian_fixedField_finrank_two J q hKcard hfixed_card

/-- For a quadratic finite-field Hermitian involution, conjugation is the
`q`-power Frobenius. This is the fixed-field bridge used in Huppert II.10.4. -/
public theorem huppert_II_10_4_conj_eq_frobenius
    {K : Type u} [Field K] [Finite K] {n : ℕ}
    (J : HermitianForm n K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    ∀ x : K, J.conj x = x ^ q := by
  classical
  let k0 := FixedBy.subfield K J.conj
  have hk0card : Nat.card k0 = q := by
    rw [card_fixedBy_subfield J, hfixed_card]
  have hq : 1 < q := by
    rw [← hk0card]
    exact Finite.one_lt_card
  have hfinrank : Module.finrank k0 K = 2 :=
    hermitian_fixedField_finrank_two J q hKcard hfixed_card
  let c : K ≃ₐ[k0] K :=
    AlgEquiv.ofRingEquiv (f := J.conj) (fun x => x.property)
  have hc_ne : c ≠ 1 := by
    intro hc
    have hconj : ∀ x : K, J.conj x = x := by
      intro x
      change c x = x
      rw [hc]
      rfl
    let e : {x : K // J.conj x = x} ≃ K :=
      { toFun := fun x => x
        invFun := fun x => ⟨x, hconj x⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun _ => rfl }
    have hcard : Nat.card {x : K // J.conj x = x} = Nat.card K :=
      Nat.card_congr e
    have hqq : q = q ^ 2 := hfixed_card.symm.trans (hcard.trans hKcard)
    nlinarith [hq]
  let fk0 : Fintype k0 := Fintype.ofFinite k0
  let fr : K ≃ₐ[k0] K :=
    @FiniteField.frobeniusAlgEquivOfAlgebraic k0 _ fk0 K _ _ _
  obtain ⟨i, hi⟩ :=
    (@FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k0 _ fk0 K _ _ _).surjective c
  have hi_bound : i.1 < 2 := by
    calc
      i.1 < Module.finrank k0 K := i.2
      _ = 2 := hfinrank
  have hi_val : i.1 = 1 := by
    by_contra hi_one
    have hi_zero : i.1 = 0 := by omega
    apply hc_ne
    rw [← hi]
    simp [hi_zero]
  have hcfr : c = fr := by
    rw [← hi]
    change fr ^ i.1 = fr
    rw [hi_val, pow_one]
  intro x
  symm
  calc
    x ^ q = x ^ Nat.card k0 := by rw [hk0card]
    _ = fr x := by
      simp [fr]
    _ = c x := by rw [hcfr]
    _ = J.conj x := rfl

/-- The norm form of Huppert II.8.7 used in II.10.4: every nonzero fixed
element is `b * conj b` for a nonzero `b`. -/
public theorem huppert_II_10_4_norm_surjective
    {K : Type u} [Field K] [Finite K] {n : ℕ}
    (J : HermitianForm n K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    ∀ a : K, J.conj a = a → a ≠ 0 →
      ∃ b : K, b ≠ 0 ∧ b * J.conj b = a := by
  classical
  let k0 := FixedBy.subfield K J.conj
  have hk0card : Nat.card k0 = q := by
    rw [card_fixedBy_subfield J, hfixed_card]
  have hfinrank : Module.finrank k0 K = 2 :=
    hermitian_fixedField_finrank_two J q hKcard hfixed_card
  have hpow : ∀ x : K, x ^ q = J.conj x := fun x =>
    (huppert_II_10_4_conj_eq_frobenius J q hKcard hfixed_card x).symm
  intro a ha ha0
  let a0 : k0 := ⟨a, by
    change J.conj a = a
    exact ha⟩
  have ha00 : a0 ≠ 0 := by
    intro hz
    apply ha0
    exact congrArg Subtype.val hz
  let au : k0ˣ := Units.mk0 a0 ha00
  obtain ⟨b, hb⟩ := huppert_II_8_7_norm_surjective k0 K au
  refine ⟨(b : K), Units.ne_zero b, ?_⟩
  have hbval := congrArg (fun z : k0ˣ => (((z : k0) : K))) hb
  have hnorm :
      algebraMap k0 K (Algebra.norm k0 (b : K)) =
        (b : K) * J.conj (b : K) := by
    rw [FiniteField.algebraMap_norm_eq_prod_pow]
    erw [hfinrank]
    simp [Finset.prod_range_succ]
    rw [hk0card, hpow]
  rw [← hnorm]
  simpa [au, a0, Subfield.algebraMap_ofSubfield] using hbval

/-- The trace form used in II.10.12: every element fixed by the quadratic
Hermitian involution is `b + conj b`. -/
public theorem huppert_II_10_4_trace_surjective
    {K : Type u} [Field K] [Finite K] {n : ℕ}
    (J : HermitianForm n K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    ∀ c : K, J.conj c = c → ∃ b : K, b + J.conj b = c := by
  classical
  let k0 := FixedBy.subfield K J.conj
  have hk0card : Nat.card k0 = q := by
    rw [card_fixedBy_subfield J, hfixed_card]
  have hfinrank : Module.finrank k0 K = 2 :=
    hermitian_fixedField_finrank_two J q hKcard hfixed_card
  have hpow : ∀ x : K, x ^ q = J.conj x := fun x =>
    (huppert_II_10_4_conj_eq_frobenius J q hKcard hfixed_card x).symm
  intro c hc
  let c0 : k0 := ⟨c, by
    change J.conj c = c
    exact hc⟩
  obtain ⟨b, hb⟩ := Algebra.trace_surjective k0 K c0
  refine ⟨b, ?_⟩
  have htrace : algebraMap k0 K (Algebra.trace k0 K b) =
      b + J.conj b := by
    rw [FiniteField.algebraMap_trace_eq_sum_pow]
    erw [hfinrank]
    simp [Finset.sum_range_succ]
    rw [hk0card, hpow]
  rw [← htrace, hb]
  rfl

private theorem hermitian_exists_trace_one
    {K : Type u} [Field K] [Finite K] {n : ℕ}
    (J : HermitianForm n K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    ∃ t : K, t + J.conj t = 1 :=
  huppert_II_10_4_trace_surjective J q hKcard hfixed_card 1 (by simp)

/-- Huppert II.10.4(a): a Hermitian space over `GF(q^2)` has an orthonormal
basis. -/
public theorem huppert_II_10_4_a_orthonormal_basis
    {K : Type u} [Field K] [Finite K] (n : ℕ)
    (J : HermitianForm n K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    ∃ P : GL (Fin n) K,
      J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
          (P : Matrix (Fin n) (Fin n) K) = 1 := by
  classical
  letI : Star K := ⟨J.conj⟩
  letI : InvolutiveStar K := ⟨J.conj_involutive⟩
  letI : StarMul K := ⟨fun r s => by
    change J.conj (r * s) = J.conj s * J.conj r
    rw [map_mul, mul_comm]⟩
  letI : StarRing K := ⟨fun r s => by
    change J.conj (r + s) = J.conj r + J.conj s
    rw [map_add]⟩
  have htrace_nonzero : ∃ a : K, a + J.conj a ≠ 0 := by
    by_contra htrace
    push Not at htrace
    have hchar : (1 : K) + 1 = 0 := by
      simpa using htrace 1
    have hconj : ∀ a : K, J.conj a = a := by
      intro a
      have ha : a + a = 0 := by
        calc
          a + a = a * ((1 : K) + 1) := by ring
          _ = 0 := by rw [hchar, mul_zero]
      exact (add_eq_zero_iff_neg_eq.mp (htrace a)).symm.trans
        (add_eq_zero_iff_neg_eq.mp ha)
    let e : {x : K // J.conj x = x} ≃ K :=
      { toFun := fun x => x
        invFun := fun x => ⟨x, hconj x⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun _ => rfl }
    have hcard : Nat.card {x : K // J.conj x = x} = Nat.card K :=
      Nat.card_congr e
    have hqcard : q = Nat.card K := hfixed_card.symm.trans hcard
    have hq : 1 < q := by
      rw [hqcard]
      exact Finite.one_lt_card
    have hqq : q = q ^ 2 := hfixed_card.symm.trans (hcard.trans hKcard)
    nlinarith [hq]
  have horthogonal_basis :=
    huppert_II_10_2_b_orthogonal_basis n J htrace_nonzero
  obtain ⟨P₀, hP₀off, hP₀diag⟩ := horthogonal_basis
  let A := J.conjTranspose (P₀ : Matrix (Fin n) (Fin n) K) * J.form *
    (P₀ : Matrix (Fin n) (Fin n) K)
  have hJhermitian : J.form.IsHermitian := by
    apply Matrix.IsHermitian.ext
    exact J.form_hermitian
  have hAhermitian : A.IsHermitian := by
    apply Matrix.isHermitian_conjTranspose_mul_mul
    exact hJhermitian
  have hAfixed (i : Fin n) : J.conj (A i i) = A i i := by
    exact hAhermitian.apply i i
  have hscale (i : Fin n) :
      ∃ d : K, d ≠ 0 ∧ d * J.conj d = (A i i)⁻¹ := by
    apply huppert_II_10_4_norm_surjective J q hKcard hfixed_card
    · simp [hAfixed]
    · exact inv_ne_zero (hP₀diag i)
  choose d hd0 hdnorm using hscale
  let Dmat : Matrix (Fin n) (Fin n) K := Matrix.diagonal d
  have hDdet : Matrix.det Dmat ≠ 0 := by
    change Matrix.det (Matrix.diagonal d) ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 i
  let D : GL (Fin n) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Dmat hDdet
  let P := P₀ * D
  refine ⟨P, ?_⟩
  have hPval :
      (P : Matrix (Fin n) (Fin n) K) =
        (P₀ : Matrix (Fin n) (Fin n) K) * Dmat := rfl
  have hstar (x : K) : star x = J.conj x := rfl
  have hconjTranspose_mul :
      J.conjTranspose ((P₀ : Matrix (Fin n) (Fin n) K) * Dmat) =
        J.conjTranspose Dmat *
          J.conjTranspose (P₀ : Matrix (Fin n) (Fin n) K) := by
    change (((P₀ : Matrix (Fin n) (Fin n) K) * Dmat)ᴴ) =
      Dmatᴴ * (P₀ : Matrix (Fin n) (Fin n) K)ᴴ
    exact Matrix.conjTranspose_mul _ _
  have hentry (i j : Fin n) :
      (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
          (P : Matrix (Fin n) (Fin n) K)) i j =
        J.conj (d i) * A i j * d j := by
    rw [hPval, hconjTranspose_mul]
    change ((Dmatᴴ * (P₀ : Matrix (Fin n) (Fin n) K)ᴴ) * J.form *
      ((P₀ : Matrix (Fin n) (Fin n) K) * Dmat)) i j = _
    rw [show (P₀ : Matrix (Fin n) (Fin n) K)ᴴ =
      J.conjTranspose (P₀ : Matrix (Fin n) (Fin n) K) by rfl]
    rw [show
      (Dmatᴴ * J.conjTranspose (P₀ : Matrix (Fin n) (Fin n) K)) * J.form *
          ((P₀ : Matrix (Fin n) (Fin n) K) * Dmat) =
        Dmatᴴ * A * Dmat by simp only [A, Matrix.mul_assoc]]
    simp [Dmat, Matrix.diagonal_mul, Matrix.mul_diagonal, hstar]
  ext i j
  rw [hentry]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq]
    calc
      J.conj (d i) * A i i * d i = A i i * (d i * J.conj (d i)) := by ring
      _ = A i i * (A i i)⁻¹ := by rw [hdnorm]
      _ = 1 := mul_inv_cancel₀ (hP₀diag i)
  · rw [Matrix.one_apply_ne hij,
      show A i j = 0 from hP₀off i j hij, mul_zero, zero_mul]

/-- Huppert II.10.4(b), in the odd-dimensional case used for `SU(3)`: a
nondegenerate Hermitian form over `GF(q^2)` admits a basis with the displayed
standard Gram matrix. -/
public theorem huppert_II_10_4_b_standard_hermitian_basis
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    ∃ P : GL (Fin 3) K,
      J.conjTranspose (P : Matrix (Fin 3) (Fin 3) K) * J.form *
          (P : Matrix (Fin 3) (Fin 3) K) =
        !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  classical
  obtain ⟨P₀, hP₀⟩ :=
    huppert_II_10_4_a_orthonormal_basis 3 J q hKcard hfixed_card
  obtain ⟨s, hs0, hs⟩ :=
    huppert_II_10_4_norm_surjective J q hKcard hfixed_card (-1) (by simp) (by simp)
  obtain ⟨t, ht⟩ :=
    hermitian_exists_trace_one J q hKcard hfixed_card
  have hs' : J.conj s * s = -1 := by rw [mul_comm, hs]
  have ht' : J.conj t + t = 1 := by rw [add_comm, ht]
  let Qmat : Matrix (Fin 3) (Fin 3) K :=
    !![1, 0, 1 - t; 0, 1, 0; s, 0, -s * t]
  have hQdet_eq : Matrix.det Qmat = -s := by
    simp [Qmat, Matrix.det_fin_three]
    ring
  have hQdet : Matrix.det Qmat ≠ 0 := by
    rw [hQdet_eq]
    exact neg_ne_zero.mpr hs0
  have hQgram :
      J.conjTranspose Qmat * Qmat =
        !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Qmat, HermitianForm.conjTranspose, Matrix.mul_apply,
        Fin.sum_univ_three] <;>
      ring_nf at hs hs' ht ht' ⊢ <;>
      simp_all
    all_goals linear_combination -ht'
  let Q : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Qmat hQdet
  let P := P₀ * Q
  refine ⟨P, ?_⟩
  have hconjTranspose_mul (X Y : Matrix (Fin 3) (Fin 3) K) :
      J.conjTranspose (X * Y) =
        J.conjTranspose Y * J.conjTranspose X := by
    ext i j
    simp only [HermitianForm.conjTranspose, Matrix.mul_apply, map_sum, map_mul]
    apply Finset.sum_bij (fun k _ => k) <;> simp [mul_comm]
  change J.conjTranspose
      ((P₀ : Matrix (Fin 3) (Fin 3) K) * Qmat) * J.form *
        ((P₀ : Matrix (Fin 3) (Fin 3) K) * Qmat) = _
  rw [hconjTranspose_mul]
  calc
    (J.conjTranspose Qmat *
          J.conjTranspose (P₀ : Matrix (Fin 3) (Fin 3) K)) * J.form *
        ((P₀ : Matrix (Fin 3) (Fin 3) K) * Qmat) =
      J.conjTranspose Qmat *
          (J.conjTranspose (P₀ : Matrix (Fin 3) (Fin 3) K) * J.form *
            (P₀ : Matrix (Fin 3) (Fin 3) K)) * Qmat := by
        simp only [Matrix.mul_assoc]
    _ = J.conjTranspose Qmat * 1 * Qmat := by rw [hP₀]
    _ = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by simpa using hQgram

end External
end CFSG.BenderSuzuki

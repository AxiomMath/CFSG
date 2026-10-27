module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGappendixC.Basic

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped Pointwise commutatorElement

noncomputable section

universe u v

variable (p q : ℕ) [Fact p.Prime]

variable (p q : ℕ) [Fact p.Prime]

/-- The finite field `F_{p^q}` used in Appendix C. -/
public abbrev CFSG.appendixCField : Type :=
  GaloisField p q

/-- The additive group of `F_{p^q}`, written multiplicatively as in Appendix C. -/
public abbrev CFSG.appendixCP : Type :=
  Multiplicative (appendixCField p q)

/-- Appendix C condition `(A)`: `((p^q - 1) / (p - 1), p - 1) = 1`. -/
@[expose] public def CFSG.appendixCConditionA : Prop :=
  Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)

/-- Appendix C Remark (I): condition `(A)` is equivalent to `q` being coprime
to `p - 1`. -/
public theorem CFSG.appendixCConditionA_iff_coprime_q_sub_one :
    appendixCConditionA p q ↔ Nat.Coprime q (p - 1) := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hpmod : p ≡ 1 [MOD p - 1] := by
    have h : (p - 1) * 1 + 1 = p := by omega
    have hme : (p - 1) * 1 + 1 ≡ 1 [MOD p - 1] := Nat.ModEq.modulus_mul_add
    rw [h] at hme
    exact hme
  have hmod : ((p ^ q - 1) / (p - 1)) ≡ q [MOD p - 1] := by
    rw [← Nat.geomSum_eq hp2 q]
    have hsum :
        (∑ k ∈ Finset.range q, p ^ k) ≡
          (∑ k ∈ Finset.range q, 1 ^ k) [MOD p - 1] := by
      apply Nat.ModEq.sum
      intro k _hk
      exact hpmod.pow k
    simpa using hsum
  have hgcd := hmod.gcd_eq
  rw [appendixCConditionA, Nat.Coprime]
  rw [hgcd]


/-- The set `E = {a in F_{p^q} | N(a) = N(2-a) = 1}`. -/
@[expose] public def CFSG.appendixCE : Set (appendixCField p q) :=
  {a | Algebra.norm (ZMod p) a = 1 ∧
    Algebra.norm (ZMod p) (2 - a) = 1}

/-- The assertion `S = S^{-1}` for a set in a field. -/
@[expose] public def CFSG.appendixCInversionStable
    (S : Set (appendixCField p q)) : Prop :=
  ∀ a, a ∈ S ↔ a⁻¹ ∈ S

/-- If `E` has at least two elements, then it has an element different from `1`. -/
public theorem CFSG.appendixCE_exists_ne_one_of_two_le_card
    (hcard : 2 ≤ Nat.card (appendixCE p q)) :
    ∃ a : appendixCField p q, a ∈ appendixCE p q ∧ a ≠ 1 := by
  by_contra h
  have hsubsingleton : Subsingleton (appendixCE p q) := by
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    have hx1 : (x : appendixCField p q) = 1 := by
      by_contra hx
      exact h ⟨x, x.property, hx⟩
    have hy1 : (y : appendixCField p q) = 1 := by
      by_contra hy
      exact h ⟨y, y.property, hy⟩
    exact hx1.trans hy1.symm
  have : Finite (appendixCE p q) := inferInstance
  have hle : Nat.card (appendixCE p q) ≤ 1 :=
    (Finite.card_le_one_iff_subsingleton (α := appendixCE p q)).2 hsubsingleton
  omega

/-- The element `1` belongs to `E`. -/
public theorem CFSG.appendixCE_one_mem :
    (1 : appendixCField p q) ∈ appendixCE p q := by
  constructor
  · simp
  · have h : (2 : appendixCField p q) - 1 = 1 := by ring
    simp [h]

/-- A non-one member of `E`, together with `1 ∈ E`, gives `|E| ≥ 2`. -/
public theorem CFSG.two_le_card_appendixCE_of_mem_ne_one
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
    2 ≤ Nat.card (appendixCE p q) := by
  let f : Fin 2 → appendixCE p q := fun i =>
    if i = 0 then ⟨1, appendixCE_one_mem (p := p) (q := q)⟩ else ⟨a, ha⟩
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, ha1, eq_comm] at hij ⊢
  have hle := Nat.card_le_card_of_injective f hf
  simpa using hle

/-- The defining set `E` is closed under `a ↦ 2 - a`. -/
public theorem CFSG.appendixCE_two_sub_mem
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    (2 : appendixCField p q) - a ∈ appendixCE p q := by
  rcases ha with ⟨haNorm, h2aNorm⟩
  constructor
  · simpa using h2aNorm
  · have h : (2 : appendixCField p q) - (2 - a) = a := by ring
    simpa [h] using haNorm

/-- In `F_{p^q}`, Frobenius fixes the prime-field element `2`. -/
public theorem CFSG.appendixCField_two_pow_prime_eq_two
    [Fact q.Prime] :
    (2 : appendixCField p q) ^ p = 2 := by
  have h := (add_pow_char_pow (R := appendixCField p q)
    (x := (1 : appendixCField p q)) (y := (1 : appendixCField p q)) (n := 1)
    (p := p))
  norm_num at h
  simpa [pow_one] using h


/-- Every member of `E` is nonzero, since its norm is `1`. -/
public theorem CFSG.appendixCE_ne_zero
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    a ≠ 0 := by
  intro hz
  have hnorm_zero :
      (Algebra.norm (ZMod p) (S := appendixCField p q)) a = 0 := by
    rw [Algebra.norm_eq_zero_iff]
    exact hz
  exact zero_ne_one (by
    rw [← hnorm_zero, ha.1])

/-- If `a ∈ E`, then `2 - a` is nonzero. -/
public theorem CFSG.appendixCE_two_sub_ne_zero
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    (2 : appendixCField p q) - a ≠ 0 :=
  appendixCE_ne_zero (p := p) (q := q) (appendixCE_two_sub_mem (p := p) (q := q) ha)

/-- Under inversion stability, the source map `τ(a) = (2 - a)⁻¹` preserves `E`. -/
public theorem CFSG.appendixCE_tau_mem
    (hE : appendixCInversionStable p q (appendixCE p q))
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    ((2 : appendixCField p q) - a)⁻¹ ∈ appendixCE p q :=
  (hE ((2 : appendixCField p q) - a)).1
    (appendixCE_two_sub_mem (p := p) (q := q) ha)

/-- The source transformation `τ(a) = (2-a)⁻¹` used in Appendix C Lemma C.1. -/
@[expose] public def CFSG.appendixCTau (a : appendixCField p q) : appendixCField p q :=
  ((2 : appendixCField p q) - a)⁻¹

/-- The linear terms `(1-a)n+1` whose norms are obtained from the `τ` iteration. -/
public def CFSG.appendixCLinearTerm (a : appendixCField p q) (n : ℕ) :
    appendixCField p q :=
  ((1 : appendixCField p q) - a) * (n : appendixCField p q) + 1

/-- If `E` is inversion-stable and `a ∈ E`, then every `τ`-iterate of `a`
remains in `E`. -/
public theorem CFSG.appendixCTau_iterate_mem
    (hE : appendixCInversionStable p q (appendixCE p q))
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    ∀ n : ℕ, (appendixCTau p q)^[n] a ∈ appendixCE p q := by
  intro n
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact appendixCE_tau_mem (p := p) (q := q) hE ih

/-- The source iteration identity in multiplicative form:
`((1-a)(n+1)+1) * τ^(n+1)(a) = (1-a)n+1`. -/
public theorem CFSG.appendixCLinearTerm_mul_tau_iterate_succ_eq
    (hE : appendixCInversionStable p q (appendixCE p q))
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    ∀ n : ℕ,
      appendixCLinearTerm p q a (n + 1) * (appendixCTau p q)^[n + 1] a =
        appendixCLinearTerm p q a n := by
  have hmem := appendixCTau_iterate_mem (p := p) (q := q) hE ha
  intro n
  induction n with
  | zero =>
      change appendixCLinearTerm p q a 1 * appendixCTau p q a =
        appendixCLinearTerm p q a 0
      have h2a : (2 : appendixCField p q) - a ≠ 0 :=
        appendixCE_two_sub_ne_zero (p := p) (q := q) ha
      dsimp [appendixCLinearTerm, appendixCTau]
      field_simp [h2a]
      ring
  | succ n ih =>
      rw [show n + 1 + 1 = Nat.succ (n + 1) by omega]
      rw [Function.iterate_succ_apply']
      have hz2 :
          (2 : appendixCField p q) - (appendixCTau p q)^[n] (appendixCTau p q a) ≠
            0 := by
        simpa [Function.iterate_succ_apply] using
          appendixCE_two_sub_ne_zero (p := p) (q := q) (hmem (n + 1))
      dsimp [appendixCLinearTerm, appendixCTau] at ih hz2 ⊢
      field_simp [hz2]
      norm_num at ih ⊢
      linear_combination ih

/-- The linear terms from the `τ` iteration all have norm one. -/
public theorem CFSG.appendixCLinearNorm_natCast_eq_one
    (hE : appendixCInversionStable p q (appendixCE p q))
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    ∀ n : ℕ,
      (Algebra.norm (ZMod p) (S := appendixCField p q))
        (appendixCLinearTerm p q a n) = 1 := by
  have hmem := appendixCTau_iterate_mem (p := p) (q := q) hE ha
  have hprod := appendixCLinearTerm_mul_tau_iterate_succ_eq
    (p := p) (q := q) hE ha
  intro n
  induction n with
  | zero =>
      simp [appendixCLinearTerm]
  | succ n ih =>
      have hmul := hprod n
      have hnorm_z :
          (Algebra.norm (ZMod p) (S := appendixCField p q))
            ((appendixCTau p q)^[n] (appendixCTau p q a)) = 1 := by
        simpa [Function.iterate_succ_apply] using (hmem (n + 1)).1
      have hnorm_mul :=
        congrArg (Algebra.norm (ZMod p) (S := appendixCField p q)) hmul
      simp [map_mul, hnorm_z, ih] at hnorm_mul
      exact hnorm_mul

/-- The degree-`q` norm polynomial from the proof of Lemma C.1, viewed over
`F_{p^q}`:
`∏ᵢ ((1-a)^(p^i) X + 1) - 1`. -/
public def CFSG.appendixCNormPoly (a : appendixCField p q) :
    Polynomial (appendixCField p q) :=
  (∏ i ∈ Finset.range q,
      (Polynomial.C (((1 : appendixCField p q) - a) ^ (p ^ i)) * Polynomial.X +
        Polynomial.C 1)) - Polynomial.C 1

/-- If `a ≠ 1`, the norm polynomial used in Lemma C.1 has degree exactly `q`. -/
public theorem CFSG.appendixCNormPoly_natDegree
    [Fact q.Prime] {a : appendixCField p q} (ha1 : a ≠ 1) :
    (appendixCNormPoly p q a).natDegree = q := by
  have honea : (1 : appendixCField p q) - a ≠ 0 := by
    intro h
    exact ha1 (sub_eq_zero.mp h).symm
  rw [appendixCNormPoly, Polynomial.natDegree_sub_C]
  calc
    (∏ i ∈ Finset.range q,
        (Polynomial.C (((1 : appendixCField p q) - a) ^ (p ^ i)) * Polynomial.X +
          Polynomial.C 1)).natDegree
        = ∑ i ∈ Finset.range q,
            ((Polynomial.C (((1 : appendixCField p q) - a) ^ (p ^ i)) *
                Polynomial.X + Polynomial.C 1) :
              Polynomial (appendixCField p q)).natDegree := by
          apply Polynomial.natDegree_prod
          intro i hi
          have hdeg :
              ((Polynomial.C (((1 : appendixCField p q) - a) ^ (p ^ i)) *
                  Polynomial.X + Polynomial.C 1) :
                Polynomial (appendixCField p q)).natDegree = 1 :=
            polynomial_natDegree_C_mul_X_add_C (F := appendixCField p q)
              (c := ((1 : appendixCField p q) - a) ^ (p ^ i)) (d := 1)
              (pow_ne_zero _ honea)
          intro hzero
          rw [hzero, Polynomial.natDegree_zero] at hdeg
          omega
    _ = ∑ i ∈ Finset.range q, 1 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact polynomial_natDegree_C_mul_X_add_C (F := appendixCField p q)
            (c := ((1 : appendixCField p q) - a) ^ (p ^ i)) (d := 1)
            (pow_ne_zero _ honea)
    _ = q := by simp

/-- Evaluating the C.1 norm polynomial on the embedded prime field gives the
corresponding finite-field norm minus one. -/
public theorem CFSG.appendixCNormPoly_eval_eq_algebraMap_norm_sub_one
    [Fact q.Prime]
    {a : appendixCField p q} (x : ZMod p) :
    (appendixCNormPoly p q a).eval (algebraMap (ZMod p) (appendixCField p q) x) =
      algebraMap (ZMod p) (appendixCField p q)
        ((Algebra.norm (ZMod p) (S := appendixCField p q))
          (((1 : appendixCField p q) - a) *
            algebraMap (ZMod p) (appendixCField p q) x + 1) - 1) := by
  have hq0 : q ≠ 0 := (Fact.out : Nat.Prime q).ne_zero
  have hnorm := FiniteField.algebraMap_norm_eq_prod_pow
    (K := ZMod p) (L := appendixCField p q)
    (x := (((1 : appendixCField p q) - a) *
            algebraMap (ZMod p) (appendixCField p q) x + 1))
  rw [map_sub, map_one]
  rw [hnorm]
  simp only [appendixCNormPoly, Polynomial.eval_sub, Polynomial.eval_C]
  rw [Polynomial.eval_prod]
  apply congrArg (fun z => z - 1)
  rw [GaloisField.finrank p hq0, Nat.card_zmod]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [add_pow_char_pow, mul_pow, ← map_pow]
  simp

/-- The remaining source iteration claim in Lemma C.1: for every prime-field
input `x`, the element `(1-a)x+1` has norm one. -/
public theorem CFSG.appendixCLinearNorm_eq_one
    [Fact q.Prime]
    (hE : appendixCInversionStable p q (appendixCE p q))
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    ∀ x : ZMod p,
      (Algebra.norm (ZMod p) (S := appendixCField p q))
        (((1 : appendixCField p q) - a) *
          algebraMap (ZMod p) (appendixCField p q) x + 1) = 1 := by
  intro x
  have hNat := appendixCLinearNorm_natCast_eq_one (p := p) (q := q) hE ha
  have : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hxalg :
      algebraMap (ZMod p) (appendixCField p q) x =
        (x.val : appendixCField p q) := by
    have hhom :
        (algebraMap (ZMod p) (appendixCField p q)) =
          ZMod.castHom (dvd_refl p) (appendixCField p q) := by
      exact RingHom.ext_zmod _ _
    rw [hhom]
    rw [ZMod.castHom_apply]
    exact ZMod.cast_eq_val x
  simpa [appendixCLinearTerm, hxalg] using hNat x.val

/-- Root statement for the norm polynomial in Lemma C.1, reduced to the source
iteration/norm claim. -/
public theorem CFSG.appendixCNormPoly_eval_algebraMap_eq_zero
    [Fact q.Prime]
    (hE : appendixCInversionStable p q (appendixCE p q))
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    ∀ x : ZMod p,
      (appendixCNormPoly p q a).eval
        (algebraMap (ZMod p) (appendixCField p q) x) = 0 := by
  intro x
  rw [appendixCNormPoly_eval_eq_algebraMap_norm_sub_one (p := p) (q := q) (a := a) x]
  rw [appendixCLinearNorm_eq_one (p := p) (q := q) hE ha x]
  simp

/-- Multiplication by a field unit, as an automorphism of the additive group of the field. -/
@[expose] public def CFSG.appendixCUnitAction :
    (appendixCField p q)ˣ →* MulAut (appendixCP p q) where
  toFun u := (LinearEquiv.smulOfUnit u).toAddEquiv.toMultiplicative
  map_one' := by
    ext x
    change ((1 : (appendixCField p q)ˣ) : appendixCField p q) *
        Multiplicative.toAdd x = Multiplicative.toAdd x
    simp
  map_mul' u v := by
    ext x
    change (((u * v : (appendixCField p q)ˣ) : appendixCField p q) *
        Multiplicative.toAdd x) =
      (u : appendixCField p q) *
        ((v : appendixCField p q) * Multiplicative.toAdd x)
    simp [mul_assoc]

/-- The subgroup `U` of elements of norm one in `F_{p^q}^*`. -/
@[expose] public def CFSG.appendixCNormOneUnits : Subgroup (appendixCField p q)ˣ :=
  (Units.map (Algebra.norm (ZMod p) (S := appendixCField p q))).ker

/-- The norm-one subgroup `U` has cardinality `(p^q - 1)/(p - 1)`. -/
public theorem CFSG.appendixCNormOneUnits_natCard
    [Fact q.Prime] :
    Nat.card (appendixCNormOneUnits p q) = (p ^ q - 1) / (p - 1) := by
  have hq0 : q ≠ 0 := (Fact.out : Nat.Prime q).ne_zero
  have hsurj : Function.Surjective
      (Units.map (Algebra.norm (ZMod p) (S := appendixCField p q))) := by
    exact FiniteField.unitsMap_norm_surjective (ZMod p) (appendixCField p q)
  rw [appendixCNormOneUnits]
  rw [natCard_ker_eq_card_div_of_surjective _ hsurj]
  rw [Nat.card_units, Nat.card_units]
  rw [GaloisField.card p q hq0, Nat.card_zmod]


/-- Under condition `(A)`, an element of the norm-one subgroup whose
`(p - 1)`st power is trivial must itself be trivial. -/
public theorem CFSG.appendixCNormOneUnits_eq_one_of_pow_sub_one_eq_one
    [Fact q.Prime]
    (hA : appendixCConditionA p q) {u : appendixCNormOneUnits p q}
    (hu : u ^ (p - 1) = 1) :
    u = 1 := by
  have hord_card : orderOf u ∣ Nat.card (appendixCNormOneUnits p q) := by
    exact orderOf_dvd_natCard u
  have hord_pm1 : orderOf u ∣ p - 1 := orderOf_dvd_of_pow_eq_one hu
  have hcop : Nat.Coprime (Nat.card (appendixCNormOneUnits p q)) (p - 1) := by
    simpa [appendixCNormOneUnits_natCard, appendixCConditionA] using hA
  have hord1 : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop hord_card hord_pm1
  exact orderOf_eq_one_iff.mp hord1

/-- Variant for the source expression `u^(1-p)=1`: it suffices to see that
the inverse has `(p - 1)`st power one. -/
public theorem CFSG.appendixCNormOneUnits_eq_one_of_inv_pow_sub_one_eq_one
    [Fact q.Prime]
    (hA : appendixCConditionA p q) {u : appendixCNormOneUnits p q}
    (hu : u⁻¹ ^ (p - 1) = 1) :
    u = 1 := by
  have hinv : u⁻¹ = 1 :=
    appendixCNormOneUnits_eq_one_of_pow_sub_one_eq_one (p := p) (q := q) hA hu
  simpa using congrArg Inv.inv hinv

/-- Membership in the Appendix C norm-one subgroup, unfolded as a norm
equation on the underlying field element. -/
public theorem CFSG.appendixCNormOneUnits_mem_iff
    (u : (appendixCField p q)ˣ) :
    u ∈ appendixCNormOneUnits p q ↔
      (Algebra.norm (ZMod p) (S := appendixCField p q))
        (u : appendixCField p q) = 1 := by
  rw [appendixCNormOneUnits, MonoidHom.mem_ker]
  constructor
  · intro h
    exact Units.ext_iff.mp h
  · intro h
    exact Units.ext h

/-- Under condition `(A)`, a nonzero prime-field element with norm one in
`F_{p^q}` is equal to `1`. This is the intersection half of the source
decomposition `F_{p^q}^* = F_p^* x U`. -/
public theorem CFSG.appendixC_primeField_norm_one_eq_one
    [Fact q.Prime]
    (hA : appendixCConditionA p q) {c : ZMod p} (hc0 : c ≠ 0)
    (hcnorm : (Algebra.norm (ZMod p) (S := appendixCField p q))
        (algebraMap (ZMod p) (appendixCField p q) c) = 1) :
    c = 1 := by
  have hfinrank : Module.finrank (ZMod p) (appendixCField p q) = q := by
    exact GaloisField.finrank p (Fact.out : Nat.Prime q).ne_zero
  have hcq : c ^ q = 1 := by
    simpa [Algebra.norm_algebraMap, hfinrank] using hcnorm
  have hcpm1 : c ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hc0
  have hordq : orderOf c ∣ q := orderOf_dvd_of_pow_eq_one hcq
  have hordpm1 : orderOf c ∣ p - 1 := orderOf_dvd_of_pow_eq_one hcpm1
  have hcop : Nat.Coprime q (p - 1) :=
    (appendixCConditionA_iff_coprime_q_sub_one (p := p) (q := q)).1 hA
  have hord1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hordq hordpm1
  exact orderOf_eq_one_iff.mp hord1

/-- A norm-one unit lying in the embedded prime field is trivial under
condition `(A)`. -/
public theorem CFSG.appendixCNormOneUnits_eq_one_of_coe_algebraMap
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (u : appendixCNormOneUnits p q) {c : ZMod p}
    (hc : ((u : (appendixCField p q)ˣ) : appendixCField p q) =
      algebraMap (ZMod p) (appendixCField p q) c) :
    u = 1 := by
  have hc0 : c ≠ 0 := by
    intro hcz
    have hu0 : ((u : (appendixCField p q)ˣ) : appendixCField p q) ≠ 0 :=
      Units.ne_zero (u : (appendixCField p q)ˣ)
    exact hu0 (by simp [hc, hcz])
  have hnorm_u :
      (Algebra.norm (ZMod p) (S := appendixCField p q))
        ((u : (appendixCField p q)ˣ) : appendixCField p q) = 1 := by
    exact (appendixCNormOneUnits_mem_iff (p := p) (q := q)
      (u : (appendixCField p q)ˣ)).1 u.property
  have hnorm_c :
      (Algebra.norm (ZMod p) (S := appendixCField p q))
        (algebraMap (ZMod p) (appendixCField p q) c) = 1 := by
    rw [← hc]
    exact hnorm_u
  have hc1 : c = 1 :=
    appendixC_primeField_norm_one_eq_one (p := p) (q := q) hA hc0 hnorm_c
  apply Subtype.ext
  apply Units.ext
  simp [hc, hc1]

/-- Under condition `(A)`, every nonzero field element is a product of an
embedded prime-field unit and a norm-one unit. This is the decomposition half
of the source statement `F_{p^q}^* = F_p^* x U`. -/
public theorem CFSG.appendixCFieldUnit_eq_primeField_mul_normOneUnit
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (z : (appendixCField p q)ˣ) :
    ∃ (c : (ZMod p)ˣ) (u : appendixCNormOneUnits p q),
      (z : appendixCField p q) =
        (algebraMap (ZMod p) (appendixCField p q) (c : ZMod p)) *
          ((u : (appendixCField p q)ˣ) : appendixCField p q) := by
  have hcop : Nat.Coprime (Nat.card (ZMod p)ˣ) q := by
    have hcop' : Nat.Coprime q (p - 1) :=
      (appendixCConditionA_iff_coprime_q_sub_one (p := p) (q := q)).1 hA
    rw [Nat.card_units, Nat.card_zmod]
    exact hcop'.symm
  let normUnits : (appendixCField p q)ˣ →* (ZMod p)ˣ :=
    Units.map (Algebra.norm (ZMod p) (S := appendixCField p q))
  let e : (ZMod p)ˣ ≃ (ZMod p)ˣ :=
    powCoprime (G := (ZMod p)ˣ) (n := q) hcop
  let c : (ZMod p)ˣ := e.symm (normUnits z)
  have hc : c ^ q = normUnits z := by
    change e c = normUnits z
    simpa [c, e] using e.apply_symm_apply (normUnits z)
  let cF : (appendixCField p q)ˣ :=
    Units.map (algebraMap (ZMod p) (appendixCField p q)) c
  let uF : (appendixCField p q)ˣ := z * cF⁻¹
  have hnorm_cF : normUnits cF = c ^ q := by
    apply Units.ext
    have hfinrank : Module.finrank (ZMod p) (appendixCField p q) = q := by
      exact GaloisField.finrank p (Fact.out : Nat.Prime q).ne_zero
    simp [normUnits, cF, Algebra.norm_algebraMap, hfinrank]
  have huF_mem : uF ∈ appendixCNormOneUnits p q := by
    rw [appendixCNormOneUnits]
    change normUnits uF = 1
    simp [normUnits, uF, hnorm_cF, hc]
  refine ⟨c, ⟨uF, huF_mem⟩, ?_⟩
  have hunit : z = cF * uF := by
    simp [uF]
  simpa [cF] using
    congrArg (fun w : (appendixCField p q)ˣ => (w : appendixCField p q)) hunit

/-- A member of `E` gives an element of the norm-one subgroup `U`. -/
public theorem CFSG.appendixCE_unit_mem_normOneUnits
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    Units.mk0 a (appendixCE_ne_zero (p := p) (q := q) ha) ∈
      appendixCNormOneUnits p q := by
  rw [appendixCNormOneUnits_mem_iff]
  simpa using ha.1

/-- The companion element `2 - a` for `a ∈ E` also gives an element of `U`. -/
public theorem CFSG.appendixCE_two_sub_unit_mem_normOneUnits
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    Units.mk0 ((2 : appendixCField p q) - a)
        (appendixCE_two_sub_ne_zero (p := p) (q := q) ha) ∈
      appendixCNormOneUnits p q := by
  rw [appendixCNormOneUnits_mem_iff]
  simpa using ha.2

/-- If `a ∈ E`, then `a⁻¹`, as a field unit, belongs to the norm-one subgroup
`U`. -/
public theorem CFSG.appendixCE_inv_unit_mem_normOneUnits
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    Units.mk0 a⁻¹ (inv_ne_zero (appendixCE_ne_zero (p := p) (q := q) ha)) ∈
      appendixCNormOneUnits p q := by
  rw [appendixCNormOneUnits_mem_iff]
  simp [Algebra.norm_inv, ha.1]

/-- If `a ∈ E`, then the source Step 4 unit `a(2-a)⁻¹` belongs to `U`. -/
public theorem CFSG.appendixCE_mul_inv_two_sub_unit_mem_normOneUnits
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    Units.mk0 (a * ((2 : appendixCField p q) - a)⁻¹)
        (mul_ne_zero (appendixCE_ne_zero (p := p) (q := q) ha)
          (inv_ne_zero (appendixCE_two_sub_ne_zero (p := p) (q := q) ha))) ∈
      appendixCNormOneUnits p q := by
  rw [appendixCNormOneUnits_mem_iff]
  simp [map_mul, Algebra.norm_inv, ha.1, ha.2]

/-- Reconstruct membership in `E` from norm-one unit witnesses for `z` and
`2 - z`. This is the final shape needed after the Step 4 product calculation
identifies `2 - T(x⁻¹)` with a norm-one unit. -/
public theorem CFSG.appendixCE_of_units_mem_normOneUnits
    {z : appendixCField p q} (hz : z ≠ 0)
    (h2z : (2 : appendixCField p q) - z ≠ 0)
    (hzU : Units.mk0 z hz ∈ appendixCNormOneUnits p q)
    (h2zU : Units.mk0 ((2 : appendixCField p q) - z) h2z ∈
      appendixCNormOneUnits p q) :
    z ∈ appendixCE p q := by
  constructor
  · exact (appendixCNormOneUnits_mem_iff (p := p) (q := q)
      (Units.mk0 z hz)).1 hzU
  · exact (appendixCNormOneUnits_mem_iff (p := p) (q := q)
      (Units.mk0 ((2 : appendixCField p q) - z) h2z)).1 h2zU


/-- A complex multiplicative character of `F_{p^q}` obtained by composing a
character of `𝔽_pˣ` with the finite-field norm. This is the character-theoretic
indicator used in the source proof of Appendix C Lemma C.2. -/
public noncomputable def CFSG.appendixCNormCharacter
    (χ : (ZMod p)ˣ →* ℂˣ) : MulChar (appendixCField p q) ℂ :=
  MulChar.ofUnitHom
    (χ.comp (Units.map (Algebra.norm (ZMod p) (S := appendixCField p q))))

/-- On nonzero field elements, `appendixCNormCharacter` evaluates the base
character on the norm. -/
public theorem CFSG.appendixCNormCharacter_apply_of_ne_zero
    (χ : (ZMod p)ˣ →* ℂˣ) {z : appendixCField p q} (hz : z ≠ 0) :
    appendixCNormCharacter p q χ z =
      (χ (Units.mk0 ((Algebra.norm (ZMod p) (S := appendixCField p q)) z)
        (by simpa [Algebra.norm_eq_zero_iff] using hz)) : ℂ) := by
  let hnorm_ne : (Algebra.norm (ZMod p) (S := appendixCField p q)) z ≠ 0 := by
    simpa [Algebra.norm_eq_zero_iff] using hz
  change (MulChar.ofUnitHom
      (χ.comp (Units.map (Algebra.norm (ZMod p) (S := appendixCField p q))))
        ((Units.mk0 z hz : (appendixCField p q)ˣ) : appendixCField p q)) = _
  rw [MulChar.ofUnitHom_coe]
  have hunit :
      (Units.map (Algebra.norm (ZMod p) (S := appendixCField p q))) (Units.mk0 z hz) =
        Units.mk0 ((Algebra.norm (ZMod p) (S := appendixCField p q)) z) hnorm_ne := by
    ext
    rfl
  simp [MonoidHom.comp_apply, hunit]

/-- The trivial base character lifts to the trivial multiplicative character
of `F_{p^q}`. -/
public theorem CFSG.appendixCNormCharacter_one :
    appendixCNormCharacter p q 1 = (1 : MulChar (appendixCField p q) ℂ) := by
  apply MulChar.ext
  intro z
  rw [appendixCNormCharacter_apply_of_ne_zero (p := p) (q := q) (χ := 1)
    (Units.ne_zero z)]
  simp

/-- A lifted norm character is trivial exactly when the base-field unit
character is trivial. -/
public theorem CFSG.appendixCNormCharacter_eq_one_iff
    [Fact q.Prime] (χ : (ZMod p)ˣ →* ℂˣ) :
    appendixCNormCharacter p q χ = (1 : MulChar (appendixCField p q) ℂ) ↔
      χ = 1 := by
  constructor
  · intro hχ
    ext u
    have hsurj : Function.Surjective
        (Units.map (Algebra.norm (ZMod p) (S := appendixCField p q))) := by
      exact FiniteField.unitsMap_norm_surjective (ZMod p) (appendixCField p q)
    rcases hsurj u with ⟨z, hz⟩
    have hval := congrArg
      (fun η : MulChar (appendixCField p q) ℂ => η (z : appendixCField p q)) hχ
    change appendixCNormCharacter p q χ (z : appendixCField p q) =
      (1 : MulChar (appendixCField p q) ℂ) (z : appendixCField p q) at hval
    rw [appendixCNormCharacter_apply_of_ne_zero (p := p) (q := q) (χ := χ)
      (Units.ne_zero z)] at hval
    let hnorm_ne :
        (Algebra.norm (ZMod p) (S := appendixCField p q))
          (z : appendixCField p q) ≠ 0 := by
      intro hzero
      exact Units.ne_zero z (Algebra.norm_eq_zero_iff.mp hzero)
    have hunit :
        Units.mk0
          ((Algebra.norm (ZMod p) (S := appendixCField p q))
            (z : appendixCField p q)) hnorm_ne = u := by
      apply Units.ext
      change (Algebra.norm (ZMod p) (S := appendixCField p q))
        (z : appendixCField p q) = (u : ZMod p)
      exact congrArg (fun w : (ZMod p)ˣ => (w : ZMod p)) hz
    simpa [hnorm_ne, hunit] using hval
  · intro hχ
    subst χ
    exact appendixCNormCharacter_one (p := p) (q := q)

/-- The inner double-norm character sum in the `E` count is a scaled Jacobi
sum. This rewrites the source summation by the change of variables `z = 2x`. -/
public theorem CFSG.appendixC_norm_character_sum_eq_twice_jacobiSum
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    (χ ψ : (ZMod p)ˣ →* ℂˣ) :
    (∑ z : appendixCField p q,
      appendixCNormCharacter p q χ z *
        appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) =
      appendixCNormCharacter p q χ (2 : appendixCField p q) *
        appendixCNormCharacter p q ψ (2 : appendixCField p q) *
          jacobiSum (appendixCNormCharacter p q χ)
            (appendixCNormCharacter p q ψ) := by
  classical
  have hp2 : p ≠ 2 := by
    rcases hoddp with ⟨k, hk⟩
    omega
  have htwo : (2 : appendixCField p q) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (appendixCField p q) Nat.prime_two hp2
  rw [← (Equiv.mulLeft₀ (2 : appendixCField p q) htwo).bijective.sum_comp
    (fun z : appendixCField p q =>
      appendixCNormCharacter p q χ z *
        appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z))]
  simp only [Equiv.mulLeft₀_apply, jacobiSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  have hsub : (2 : appendixCField p q) - 2 * x = 2 * (1 - x) := by ring
  rw [hsub]
  rw [map_mul, map_mul]
  ring

/-- The trivial-trivial term in the Appendix C Lemma C.2 character sum is
`p^q - 2`, corresponding to all nonzero `z` with `2 - z` nonzero. -/
public theorem CFSG.appendixC_norm_character_trivial_trivial_sum
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p) :
    (∑ z : appendixCField p q,
      appendixCNormCharacter p q 1 z *
        appendixCNormCharacter p q 1 ((2 : appendixCField p q) - z)) =
      (p ^ q - 2 : ℂ) := by
  have hp2 : p ≠ 2 := by
    rcases hoddp with ⟨k, hk⟩
    omega
  have htwo : (2 : appendixCField p q) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (appendixCField p q) Nat.prime_two hp2
  have hone_two :
      (1 : MulChar (appendixCField p q) ℂ) (2 : appendixCField p q) = 1 :=
    MulChar.one_apply (isUnit_iff_ne_zero.mpr htwo)
  have hcard : Fintype.card (appendixCField p q) = p ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p q (Fact.out : Nat.Prime q).ne_zero
  have hsum := appendixC_norm_character_sum_eq_twice_jacobiSum
    (p := p) (q := q) hoddp (1 : (ZMod p)ˣ →* ℂˣ) 1
  simpa [appendixCNormCharacter_one, jacobiSum_one_one, hone_two, hcard] using hsum

/-- The one-trivial, one-nontrivial terms in the Appendix C Lemma C.2
character sum reduce to a single norm-character value. -/
public theorem CFSG.appendixC_norm_character_trivial_nontrivial_sum
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    {ψ : (ZMod p)ˣ →* ℂˣ} (hψ : ψ ≠ 1) :
    (∑ z : appendixCField p q,
      appendixCNormCharacter p q 1 z *
        appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) =
      - appendixCNormCharacter p q ψ (2 : appendixCField p q) := by
  have hp2 : p ≠ 2 := by
    rcases hoddp with ⟨k, hk⟩
    omega
  have htwo : (2 : appendixCField p q) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (appendixCField p q) Nat.prime_two hp2
  have hone_two :
      (1 : MulChar (appendixCField p q) ℂ) (2 : appendixCField p q) = 1 :=
    MulChar.one_apply (isUnit_iff_ne_zero.mpr htwo)
  have hψ' : appendixCNormCharacter p q ψ ≠
      (1 : MulChar (appendixCField p q) ℂ) := by
    intro h
    exact hψ ((appendixCNormCharacter_eq_one_iff (p := p) (q := q) ψ).1 h)
  have hsum := appendixC_norm_character_sum_eq_twice_jacobiSum
    (p := p) (q := q) hoddp (1 : (ZMod p)ˣ →* ℂˣ) ψ
  simpa [appendixCNormCharacter_one, jacobiSum_one_nontrivial hψ', hone_two] using hsum

/-- The symmetric one-nontrivial, one-trivial term in the Appendix C Lemma C.2
character sum. -/
public theorem CFSG.appendixC_norm_character_nontrivial_trivial_sum
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    {χ : (ZMod p)ˣ →* ℂˣ} (hχ : χ ≠ 1) :
    (∑ z : appendixCField p q,
      appendixCNormCharacter p q χ z *
        appendixCNormCharacter p q 1 ((2 : appendixCField p q) - z)) =
      - appendixCNormCharacter p q χ (2 : appendixCField p q) := by
  have hp2 : p ≠ 2 := by
    rcases hoddp with ⟨k, hk⟩
    omega
  have htwo : (2 : appendixCField p q) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (appendixCField p q) Nat.prime_two hp2
  have hone_two :
      (1 : MulChar (appendixCField p q) ℂ) (2 : appendixCField p q) = 1 :=
    MulChar.one_apply (isUnit_iff_ne_zero.mpr htwo)
  have hχ' : appendixCNormCharacter p q χ ≠
      (1 : MulChar (appendixCField p q) ℂ) := by
    intro h
    exact hχ ((appendixCNormCharacter_eq_one_iff (p := p) (q := q) χ).1 h)
  have hJ : jacobiSum (appendixCNormCharacter p q χ)
      (1 : MulChar (appendixCField p q) ℂ) = -1 := by
    rw [jacobiSum_comm]
    exact jacobiSum_one_nontrivial hχ'
  have hsum := appendixC_norm_character_sum_eq_twice_jacobiSum
    (p := p) (q := q) hoddp χ (1 : (ZMod p)ˣ →* ℂˣ)
  simpa [appendixCNormCharacter_one, hJ, hone_two, mul_comm, mul_left_comm, mul_assoc]
    using hsum

/-- Complex conjugation sends a Jacobi sum to the Jacobi sum of the inverse
characters. -/
public theorem CFSG.appendixC_jacobiSum_star_eq_jacobiSum_inv
    {F : Type*} [Field F] [Fintype F]
    (χ ψ : MulChar F ℂ) :
    star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
  classical
  simp [jacobiSum, MulChar.star_apply']

/-- The standard Jacobi-sum norm-square bound in the nontrivial case, stated
as an equality for complex-valued characters. -/
public theorem CFSG.appendixC_jacobiSum_norm_sq
    {F : Type*} [Field F] [Fintype F] [Finite Fˣ]
    (hchar : ringChar ℂ ≠ ringChar F)
    {χ ψ : MulChar F ℂ} (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  classical
  have hmul : jacobiSum χ ψ * jacobiSum χ⁻¹ ψ⁻¹ = (Fintype.card F : ℂ) :=
    jacobiSum_mul_jacobiSum_inv hchar hχ hψ hχψ
  have hC : ((Complex.normSq (jacobiSum χ ψ) : ℝ) : ℂ) =
      (Fintype.card F : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    change star (jacobiSum χ ψ) * jacobiSum χ ψ = (Fintype.card F : ℂ)
    rw [appendixC_jacobiSum_star_eq_jacobiSum_inv]
    simpa [mul_comm] using hmul
  have hR : Complex.normSq (jacobiSum χ ψ) = (Fintype.card F : ℝ) :=
    Complex.ofReal_inj.mp hC
  simpa [Complex.normSq_eq_norm_sq] using hR

/-- Lifting base-field unit characters along the norm map preserves products. -/
public theorem CFSG.appendixCNormCharacter_mul
    (χ ψ : (ZMod p)ˣ →* ℂˣ) :
    appendixCNormCharacter p q (χ * ψ) =
      appendixCNormCharacter p q χ * appendixCNormCharacter p q ψ := by
  ext z
  simp [appendixCNormCharacter_apply_of_ne_zero (p := p) (q := q), Units.ne_zero z]

/-- Lifting base-field unit characters along the norm map preserves inversion. -/
public theorem CFSG.appendixCNormCharacter_inv
    (χ : (ZMod p)ˣ →* ℂˣ) :
    appendixCNormCharacter p q χ⁻¹ = (appendixCNormCharacter p q χ)⁻¹ := by
  ext z
  rw [MulChar.inv_apply_eq_inv']
  rw [appendixCNormCharacter_apply_of_ne_zero (p := p) (q := q) (χ := χ⁻¹)
    (Units.ne_zero z)]
  rw [appendixCNormCharacter_apply_of_ne_zero (p := p) (q := q) (χ := χ)
    (Units.ne_zero z)]
  simp

/-- Values of base-field unit characters have complex norm one. -/
public theorem CFSG.appendixC_unit_character_norm
    (χ : (ZMod p)ˣ →* ℂˣ) (u : (ZMod p)ˣ) : ‖(χ u : ℂ)‖ = 1 := by
  let n := Fintype.card (ZMod p)ˣ
  have hn : NeZero n := ⟨Fintype.card_ne_zero⟩
  have hroot : χ u ∈ rootsOfUnity n ℂ := by
    rw [mem_rootsOfUnity]
    change (χ u) ^ n = 1
    rw [← map_pow, pow_card_eq_one]
    simp
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (n := n) hroot

/-- Lifted norm characters have norm-one values away from zero. -/
public theorem CFSG.appendixCNormCharacter_norm_apply_of_ne_zero
    (χ : (ZMod p)ˣ →* ℂˣ) {z : appendixCField p q} (hz : z ≠ 0) :
    ‖appendixCNormCharacter p q χ z‖ = 1 := by
  rw [appendixCNormCharacter_apply_of_ne_zero (p := p) (q := q) (χ := χ) hz]
  exact appendixC_unit_character_norm (p := p) χ _

/-- The complex character group of `𝔽_pˣ` has cardinality `p - 1`. -/
public theorem CFSG.appendixC_character_group_natCard :
    Nat.card ((ZMod p)ˣ →* ℂˣ) = p - 1 := by
  classical
  have hexp : Monoid.ExponentExists (ZMod p)ˣ := Monoid.ExponentExists.of_finite
  have : NeZero (Monoid.exponent (ZMod p)ˣ) := ⟨(Monoid.exponent_ne_zero.2 hexp)⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod p)ˣ) :=
    appendixC_complex_hasEnoughRootsOfUnity (Monoid.exponent (ZMod p)ˣ)
  calc
    Nat.card ((ZMod p)ˣ →* ℂˣ) = Nat.card (ZMod p)ˣ :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (ZMod p)ˣ ℂ
    _ = Fintype.card (ZMod p)ˣ := Nat.card_eq_fintype_card
    _ = p - 1 := ZMod.card_units p

/-- The nontrivial complex characters of `𝔽_pˣ` have cardinality `p - 2`. -/
public theorem CFSG.appendixC_nontrivial_character_natCard :
    Nat.card {χ : (ZMod p)ˣ →* ℂˣ // χ ≠ 1} = p - 2 := by
  classical
  let : Fintype ((ZMod p)ˣ →* ℂˣ) := Fintype.ofFinite _
  let : Fintype {χ : (ZMod p)ˣ →* ℂˣ // χ ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have hcompl := Fintype.card_subtype_compl (fun χ : (ZMod p)ˣ →* ℂˣ => χ = 1)
  rw [hcompl]
  have hone : Fintype.card {χ : (ZMod p)ˣ →* ℂˣ // χ = 1} = 1 := by
    exact Fintype.card_ofSubsingleton ⟨1, rfl⟩
  rw [hone]
  rw [← Nat.card_eq_fintype_card, appendixC_character_group_natCard (p := p)]
  omega

/-- For a fixed nontrivial base-field character, the nontrivial characters
which are not its inverse have cardinality `p - 3`. -/
public theorem CFSG.appendixC_nontrivial_noninverse_character_natCard
    (hoddp : Odd p) {χ : (ZMod p)ˣ →* ℂˣ} (hχ : χ ≠ 1) :
    Nat.card {ψ : (ZMod p)ˣ →* ℂˣ // ψ ≠ 1 ∧ χ * ψ ≠ 1} = p - 3 := by
  classical
  have hχinv : χ⁻¹ ≠ (1 : (ZMod p)ˣ →* ℂˣ) := by
    intro h
    apply hχ
    ext u
    have hu : (χ u)⁻¹ = (1 : ℂˣ) := by
      simpa using congrArg (fun ψ : (ZMod p)ˣ →* ℂˣ => ψ u) h
    simpa using inv_eq_one.mp hu
  let e : {ψ : (ZMod p)ˣ →* ℂˣ // ψ ≠ 1 ∧ χ * ψ ≠ 1} ≃
      {ψ : (ZMod p)ˣ →* ℂˣ // ψ ≠ 1 ∧ ψ ≠ χ⁻¹} :=
    { toFun := fun ψ => ⟨ψ.1, ψ.2.1, by
        intro hψ
        exact ψ.2.2 (by rw [hψ]; exact mul_inv_cancel χ)⟩
      invFun := fun ψ => ⟨ψ.1, ψ.2.1, by
        intro hmul
        apply ψ.2.2
        ext u
        have hval : χ u * ψ.1 u = 1 := by
          simpa [MonoidHom.mul_apply] using congrFun (congrArg DFunLike.coe hmul) u
        calc
          ((ψ.1 u : ℂˣ) : ℂ) =
              (((χ u)⁻¹ * (χ u * ψ.1 u) : ℂˣ) : ℂ) := by group
          _ = (((χ u)⁻¹ : ℂˣ) : ℂ) := by rw [hval]; simp
          _ = (((χ⁻¹) u : ℂˣ) : ℂ) := by simp [MonoidHom.inv_apply]⟩
      left_inv := by intro ψ; rfl
      right_inv := by intro ψ; rfl }
  rw [Nat.card_congr e]
  let : Fintype ((ZMod p)ˣ →* ℂˣ) := Fintype.ofFinite _
  let : Fintype {ψ : (ZMod p)ˣ →* ℂˣ // ψ ≠ 1 ∧ ψ ≠ χ⁻¹} :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have hcardX : Fintype.card ((ZMod p)ˣ →* ℂˣ) = p - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact appendixC_character_group_natCard (p := p)
  have hcard1 :
      Fintype.card {ψ : (ZMod p)ˣ →* ℂˣ // ψ = 1 ∨ ψ = χ⁻¹} = 2 := by
    exact Fintype.card_subtype_eq_or_eq_of_ne hχinv.symm
  have hcompl := Fintype.card_subtype_compl
    (fun ψ : (ZMod p)ˣ →* ℂˣ => ψ = 1 ∨ ψ = χ⁻¹)
  have htarget :
      Fintype.card {ψ : (ZMod p)ˣ →* ℂˣ // ψ ≠ 1 ∧ ψ ≠ χ⁻¹} =
        Fintype.card ((ZMod p)ˣ →* ℂˣ) - 2 := by
    simpa [not_or, hcard1] using hcompl
  rw [htarget, hcardX]
  have hp3 : 3 ≤ p := by
    rcases hoddp with ⟨k, hk⟩
    have hp2 := (Fact.out : Nat.Prime p).two_le
    omega
  omega

/-- The number of ordered nontrivial, non-inverse character pairs is
`(p - 2) * (p - 3)`. -/
public theorem CFSG.appendixC_nontrivial_noninverse_character_pair_natCard
    (hoddp : Odd p) :
    Nat.card {x : ((ZMod p)ˣ →* ℂˣ) × ((ZMod p)ˣ →* ℂˣ) //
      x.1 ≠ 1 ∧ x.2 ≠ 1 ∧ x.1 * x.2 ≠ 1} = (p - 2) * (p - 3) := by
  classical
  let e : {x : ((ZMod p)ˣ →* ℂˣ) × ((ZMod p)ˣ →* ℂˣ) //
      x.1 ≠ 1 ∧ x.2 ≠ 1 ∧ x.1 * x.2 ≠ 1} ≃
      Σ χ : {χ : (ZMod p)ˣ →* ℂˣ // χ ≠ 1},
        {ψ : (ZMod p)ˣ →* ℂˣ // ψ ≠ 1 ∧ χ.1 * ψ ≠ 1} :=
    { toFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2.1, x.2.2.2⟩⟩
      invFun := fun y => ⟨(y.1.1, y.2.1), y.1.2, y.2.2.1, y.2.2.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro y; rfl }
  rw [Nat.card_congr e]
  let : Fintype {χ : (ZMod p)ˣ →* ℂˣ // χ ≠ 1} := Fintype.ofFinite _
  have : ∀ χ : {χ : (ZMod p)ˣ →* ℂˣ // χ ≠ 1},
      Fintype {ψ : (ZMod p)ˣ →* ℂˣ // ψ ≠ 1 ∧ χ.1 * ψ ≠ 1} :=
    fun _ => Fintype.ofFinite _
  rw [Nat.card_sigma]
  calc
    (∑ χ : {χ : (ZMod p)ˣ →* ℂˣ // χ ≠ 1},
      Nat.card {ψ : (ZMod p)ˣ →* ℂˣ // ψ ≠ 1 ∧ χ.1 * ψ ≠ 1}) =
        ∑ _χ : {χ : (ZMod p)ˣ →* ℂˣ // χ ≠ 1}, (p - 3) := by
          apply Finset.sum_congr rfl
          intro χ _hχ
          exact appendixC_nontrivial_noninverse_character_natCard
            (p := p) hoddp χ.2
    _ = (p - 2) * (p - 3) := by
          rw [Finset.sum_const, Finset.card_univ]
          rw [← Nat.card_eq_fintype_card]
          rw [appendixC_nontrivial_character_natCard (p := p)]
          simp

/-- The nontrivial Jacobi sums appearing in the Appendix C norm-character
count have complex norm-square `p^q`. -/
public theorem CFSG.appendixC_norm_character_jacobiSum_norm_sq
    [Fact q.Prime] [Fintype (appendixCField p q)]
    {χ ψ : (ZMod p)ˣ →* ℂˣ}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖jacobiSum (appendixCNormCharacter p q χ)
        (appendixCNormCharacter p q ψ)‖ ^ 2 = (p ^ q : ℝ) := by
  classical
  have hchar : ringChar ℂ ≠ ringChar (appendixCField p q) := by
    have hp : Nat.Prime p := Fact.out
    rw [ringChar.eq_zero, ringChar.eq (appendixCField p q) p]
    exact hp.ne_zero.symm
  have hχ' : appendixCNormCharacter p q χ ≠
      (1 : MulChar (appendixCField p q) ℂ) := by
    intro h
    exact hχ ((appendixCNormCharacter_eq_one_iff (p := p) (q := q) χ).1 h)
  have hψ' : appendixCNormCharacter p q ψ ≠
      (1 : MulChar (appendixCField p q) ℂ) := by
    intro h
    exact hψ ((appendixCNormCharacter_eq_one_iff (p := p) (q := q) ψ).1 h)
  have hχψ' : appendixCNormCharacter p q χ * appendixCNormCharacter p q ψ ≠
      (1 : MulChar (appendixCField p q) ℂ) := by
    intro h
    apply hχψ
    apply (appendixCNormCharacter_eq_one_iff (p := p) (q := q) (χ * ψ)).1
    rw [appendixCNormCharacter_mul]
    exact h
  have hnorm := appendixC_jacobiSum_norm_sq (F := appendixCField p q) hchar
    hχ' hψ' hχψ'
  have hcard : Fintype.card (appendixCField p q) = p ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p q (Fact.out : Nat.Prime q).ne_zero
  simpa [hcard] using hnorm

/-- The inverse-pair terms in the Appendix C Lemma C.2 character sum reduce
to the standard `J(χ, χ⁻¹)` value. -/
public theorem CFSG.appendixC_norm_character_inverse_pair_sum
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    {χ : (ZMod p)ˣ →* ℂˣ} (hχ : χ ≠ 1) :
    (∑ z : appendixCField p q,
      appendixCNormCharacter p q χ z *
        appendixCNormCharacter p q χ⁻¹ ((2 : appendixCField p q) - z)) =
      - appendixCNormCharacter p q χ (-1 : appendixCField p q) := by
  have hp2 : p ≠ 2 := by
    rcases hoddp with ⟨k, hk⟩
    omega
  have htwo : (2 : appendixCField p q) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (appendixCField p q) Nat.prime_two hp2
  have hχtwo_ne : appendixCNormCharacter p q χ (2 : appendixCField p q) ≠ 0 := by
    rw [appendixCNormCharacter_apply_of_ne_zero (p := p) (q := q) (χ := χ) htwo]
    exact Units.ne_zero _
  have hχ' : appendixCNormCharacter p q χ ≠
      (1 : MulChar (appendixCField p q) ℂ) := by
    intro h
    exact hχ ((appendixCNormCharacter_eq_one_iff (p := p) (q := q) χ).1 h)
  rw [appendixCNormCharacter_inv]
  have hsum := appendixC_norm_character_sum_eq_twice_jacobiSum
    (p := p) (q := q) hoddp χ χ⁻¹
  rw [appendixCNormCharacter_inv] at hsum
  simpa [jacobiSum_nontrivial_inv hχ', MulChar.inv_apply_eq_inv', htwo, hχtwo_ne,
    mul_comm, mul_left_comm, mul_assoc] using hsum

/-- The one-trivial C.2 character-sum terms have norm one. -/
public theorem CFSG.appendixC_norm_character_trivial_nontrivial_sum_norm
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    {ψ : (ZMod p)ˣ →* ℂˣ} (hψ : ψ ≠ 1) :
    ‖(∑ z : appendixCField p q,
      appendixCNormCharacter p q 1 z *
        appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z))‖ = 1 := by
  have hp2 : p ≠ 2 := by
    rcases hoddp with ⟨k, hk⟩
    omega
  have htwo : (2 : appendixCField p q) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (appendixCField p q) Nat.prime_two hp2
  rw [appendixC_norm_character_trivial_nontrivial_sum (p := p) (q := q) hoddp hψ]
  rw [norm_neg]
  exact appendixCNormCharacter_norm_apply_of_ne_zero (p := p) (q := q) ψ htwo

/-- The symmetric one-trivial C.2 character-sum terms have norm one. -/
public theorem CFSG.appendixC_norm_character_nontrivial_trivial_sum_norm
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    {χ : (ZMod p)ˣ →* ℂˣ} (hχ : χ ≠ 1) :
    ‖(∑ z : appendixCField p q,
      appendixCNormCharacter p q χ z *
        appendixCNormCharacter p q 1 ((2 : appendixCField p q) - z))‖ = 1 := by
  have hp2 : p ≠ 2 := by
    rcases hoddp with ⟨k, hk⟩
    omega
  have htwo : (2 : appendixCField p q) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (appendixCField p q) Nat.prime_two hp2
  rw [appendixC_norm_character_nontrivial_trivial_sum (p := p) (q := q) hoddp hχ]
  rw [norm_neg]
  exact appendixCNormCharacter_norm_apply_of_ne_zero (p := p) (q := q) χ htwo

/-- The inverse-pair C.2 character-sum terms have norm one. -/
public theorem CFSG.appendixC_norm_character_inverse_pair_sum_norm
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    {χ : (ZMod p)ˣ →* ℂˣ} (hχ : χ ≠ 1) :
    ‖(∑ z : appendixCField p q,
      appendixCNormCharacter p q χ z *
        appendixCNormCharacter p q χ⁻¹ ((2 : appendixCField p q) - z))‖ = 1 := by
  have hneg : (-1 : appendixCField p q) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [appendixC_norm_character_inverse_pair_sum (p := p) (q := q) hoddp hχ]
  rw [norm_neg]
  exact appendixCNormCharacter_norm_apply_of_ne_zero (p := p) (q := q) χ hneg

/-- The genuinely nontrivial, non-inverse C.2 character-sum terms have
norm-square `p^q`. -/
public theorem CFSG.appendixC_norm_character_nontrivial_noninverse_sum_norm_sq
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    {χ ψ : (ZMod p)ˣ →* ℂˣ}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖(∑ z : appendixCField p q,
      appendixCNormCharacter p q χ z *
        appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z))‖ ^ 2 =
      (p ^ q : ℝ) := by
  have hp2 : p ≠ 2 := by
    rcases hoddp with ⟨k, hk⟩
    omega
  have htwo : (2 : appendixCField p q) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (appendixCField p q) Nat.prime_two hp2
  rw [appendixC_norm_character_sum_eq_twice_jacobiSum (p := p) (q := q) hoddp χ ψ]
  rw [norm_mul, norm_mul]
  rw [appendixCNormCharacter_norm_apply_of_ne_zero (p := p) (q := q) χ htwo]
  rw [appendixCNormCharacter_norm_apply_of_ne_zero (p := p) (q := q) ψ htwo]
  simp [appendixC_norm_character_jacobiSum_norm_sq (p := p) (q := q) hχ hψ hχψ]

/-- A one-sided norm bound for the genuinely nontrivial, non-inverse C.2
character-sum terms, using only an integer exponent. -/
public theorem CFSG.appendixC_norm_character_nontrivial_noninverse_sum_norm_le
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    {χ ψ : (ZMod p)ˣ →* ℂˣ}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖(∑ z : appendixCField p q,
      appendixCNormCharacter p q χ z *
        appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z))‖ ≤
      (p ^ (q / 2 + 1) : ℝ) := by
  have hsq := appendixC_norm_character_nontrivial_noninverse_sum_norm_sq
    (p := p) (q := q) hoddp hχ hψ hχψ
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hexp : q ≤ 2 * (q / 2 + 1) := by omega
  have hpow_nat : p ^ q ≤ p ^ (2 * (q / 2 + 1)) :=
    Nat.pow_le_pow_right hp_pos hexp
  have hpow_id :
      (p ^ (q / 2 + 1) : ℝ) ^ 2 =
        (p ^ (2 * (q / 2 + 1)) : ℝ) := by
    calc
      (p ^ (q / 2 + 1) : ℝ) ^ 2 =
          ((p : ℝ) ^ (q / 2 + 1)) ^ 2 := rfl
      _ = (p : ℝ) ^ ((q / 2 + 1) * 2) := by rw [pow_mul]
      _ = (p : ℝ) ^ (2 * (q / 2 + 1)) := by rw [mul_comm]
      _ = (p ^ (2 * (q / 2 + 1)) : ℝ) := rfl
  have hpow_real : (p ^ q : ℝ) ≤ (p ^ (q / 2 + 1) : ℝ) ^ 2 := by
    rw [hpow_id]
    exact_mod_cast hpow_nat
  have hsqle :
      ‖(∑ z : appendixCField p q,
        appendixCNormCharacter p q χ z *
          appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z))‖ ^ 2 ≤
        (p ^ (q / 2 + 1) : ℝ) ^ 2 := by
    rw [hsq]
    exact hpow_real
  have habs := (sq_le_sq.mp hsqle)
  have hright_nonneg : 0 ≤ (p ^ (q / 2 + 1) : ℝ) := by positivity
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hright_nonneg] using habs

/-- Outside the trivial-trivial term, any norm-character summand which is not
genuinely nontrivial/non-inverse has norm at most one. -/
public theorem CFSG.appendixC_norm_character_pair_sum_norm_le_one_of_not_nontrivial_noninverse
    [Fact q.Prime] [Fintype (appendixCField p q)] (hoddp : Odd p)
    {χ ψ : (ZMod p)ˣ →* ℂˣ}
    (hpair : (χ, ψ) ≠ ((1 : (ZMod p)ˣ →* ℂˣ), 1))
    (hsmall : ¬ (χ ≠ 1 ∧ ψ ≠ 1 ∧ χ * ψ ≠ 1)) :
    ‖(∑ z : appendixCField p q,
      appendixCNormCharacter p q χ z *
        appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z))‖ ≤
      (1 : ℝ) := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    have hψ : ψ ≠ 1 := by
      intro hψ
      apply hpair
      simp [hψ]
    exact le_of_eq
      (appendixC_norm_character_trivial_nontrivial_sum_norm
        (p := p) (q := q) hoddp hψ)
  · by_cases hψ : ψ = 1
    · subst ψ
      exact le_of_eq
        (appendixC_norm_character_nontrivial_trivial_sum_norm
          (p := p) (q := q) hoddp hχ)
    · have hχψ : χ * ψ = 1 := by
        by_contra hne
        exact hsmall ⟨hχ, hψ, hne⟩
      have hψeq : ψ = χ⁻¹ := by
        ext u
        have hval : χ u * ψ u = 1 := by
          simpa [MonoidHom.mul_apply] using congrFun (congrArg DFunLike.coe hχψ) u
        change (ψ u : ℂ) = ((χ⁻¹) u : ℂ)
        rw [MonoidHom.inv_apply]
        exact congrArg (fun x : ℂˣ => (x : ℂ)) (eq_inv_of_mul_eq_one_right hval)
      rw [hψeq]
      exact le_of_eq
        (appendixC_norm_character_inverse_pair_sum_norm
          (p := p) (q := q) hoddp hχ)

/-- The ordered genuinely nontrivial/non-inverse character pairs have the same
cardinality when counted by the explicit product finset. -/
public theorem CFSG.appendixC_nontrivial_noninverse_character_pair_finset_card
    [Fintype ((ZMod p)ˣ →* ℂˣ)] [DecidableEq ((ZMod p)ˣ →* ℂˣ)]
    (hoddp : Odd p) :
    ((Finset.univ : Finset (((ZMod p)ˣ →* ℂˣ) × ((ZMod p)ˣ →* ℂˣ))).filter
      (fun x => x.1 ≠ 1 ∧ x.2 ≠ 1 ∧ x.1 * x.2 ≠ 1)).card =
        (p - 2) * (p - 3) := by
  classical
  rw [← Fintype.card_subtype]
  rw [← Nat.card_eq_fintype_card]
  exact appendixC_nontrivial_noninverse_character_pair_natCard (p := p) hoddp

/-- Coarse aggregate bound for the non-trivial-trivial remainder in the
Appendix C C.2 norm-character double sum. The small exceptional terms are
bounded by one and overcounted by all character pairs; the genuinely
nontrivial/non-inverse terms use the Jacobi-sum norm bound. -/
public theorem CFSG.appendixC_character_sum_remainder_norm_bound
    [Fact q.Prime] [Fintype (appendixCField p q)]
    [Fintype ((ZMod p)ˣ →* ℂˣ)] [DecidableEq ((ZMod p)ˣ →* ℂˣ)]
    (hoddp : Odd p) :
    ‖((Finset.univ :
      Finset (((ZMod p)ˣ →* ℂˣ) × ((ZMod p)ˣ →* ℂˣ))).erase
        (((1 : (ZMod p)ˣ →* ℂˣ), 1))).sum (fun x =>
      ∑ z : appendixCField p q,
          appendixCNormCharacter p q x.1 z *
          appendixCNormCharacter p q x.2 ((2 : appendixCField p q) - z))‖ ≤
      (((p - 1) * (p - 1) : ℕ) : ℝ) +
        (((p - 2) * (p - 3) : ℕ) : ℝ) * (p ^ (q / 2 + 1) : ℝ) := by
  classical
  let X := (ZMod p)ˣ →* ℂˣ
  let pairOne : X × X := ((1 : X), 1)
  let pairs : Finset (X × X) := (Finset.univ : Finset (X × X)).erase pairOne
  let pred : X × X → Prop := fun x => x.1 ≠ 1 ∧ x.2 ≠ 1 ∧ x.1 * x.2 ≠ 1
  let term : X × X → ℂ := fun x =>
    ∑ z : appendixCField p q,
      appendixCNormCharacter p q x.1 z *
        appendixCNormCharacter p q x.2 ((2 : appendixCField p q) - z)
  let big : Finset (X × X) := pairs.filter pred
  change ‖pairs.sum term‖ ≤
      (((p - 1) * (p - 1) : ℕ) : ℝ) +
        (((p - 2) * (p - 3) : ℕ) : ℝ) * (p ^ (q / 2 + 1) : ℝ)
  have hpairs_card_le : pairs.card ≤ (p - 1) * (p - 1) := by
    calc
      pairs.card ≤ Fintype.card (X × X) := Finset.card_le_univ pairs
      _ = (p - 1) * (p - 1) := by
        have hXcard : Fintype.card X = p - 1 := by
          rw [← Nat.card_eq_fintype_card]
          exact appendixC_character_group_natCard (p := p)
        simp [X, Fintype.card_prod, hXcard]
  have hbig_card : big.card = (p - 2) * (p - 3) := by
    have hbig_eq :
        big =
          (Finset.univ : Finset (X × X)).filter pred := by
      ext x
      by_cases hx : pred x
      · have hx_ne : x ≠ pairOne := by
          intro hxone
          have hx1 : x.1 = 1 := by simpa [pairOne] using congrArg Prod.fst hxone
          exact hx.1 hx1
        simp [big, pairs, pred, hx, hx_ne]
      · simp [big, pred, hx]
    rw [hbig_eq]
    simpa [X, pred] using
      appendixC_nontrivial_noninverse_character_pair_finset_card (p := p) hoddp
  have hnorm := norm_sum_le pairs term
  calc
    ‖pairs.sum term‖ ≤ pairs.sum (fun x => ‖term x‖) := hnorm
    _ ≤ pairs.sum (fun x => if pred x then (p ^ (q / 2 + 1) : ℝ) else 1) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxpair : x ≠ pairOne := by
        simpa [pairs] using (Finset.mem_erase.mp hx).1
      by_cases hxpred : pred x
      · have hle := appendixC_norm_character_nontrivial_noninverse_sum_norm_le
          (p := p) (q := q) hoddp hxpred.1 hxpred.2.1 hxpred.2.2
        simpa [term, pred, hxpred] using hle
      · have hle :=
          appendixC_norm_character_pair_sum_norm_le_one_of_not_nontrivial_noninverse
            (p := p) (q := q) hoddp (χ := x.1) (ψ := x.2)
            (by simpa [pairOne] using hxpair) (by simpa [pred] using hxpred)
        simpa [term, pred, hxpred] using hle
    _ ≤ (((p - 1) * (p - 1) : ℕ) : ℝ) +
        (((p - 2) * (p - 3) : ℕ) : ℝ) * (p ^ (q / 2 + 1) : ℝ) := by
      have hsum :
          pairs.sum (fun x => if pred x then (p ^ (q / 2 + 1) : ℝ) else 1) =
            ((pairs.filter pred).card : ℝ) * (p ^ (q / 2 + 1) : ℝ) +
              (((pairs.filter fun x => ¬ pred x).card : ℕ) : ℝ) := by
        rw [Finset.sum_ite]
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [hsum]
      have hsmall_card_le :
          (pairs.filter fun x => ¬ pred x).card ≤ pairs.card :=
        Finset.card_filter_le _ _
      have hsmall_le :
          (((pairs.filter fun x => ¬ pred x).card : ℕ) : ℝ) ≤
            (((p - 1) * (p - 1) : ℕ) : ℝ) := by
        exact_mod_cast hsmall_card_le.trans hpairs_card_le
      have hbig_le :
          ((pairs.filter pred).card : ℝ) * (p ^ (q / 2 + 1) : ℝ) ≤
            (((p - 2) * (p - 3) : ℕ) : ℝ) *
              (p ^ (q / 2 + 1) : ℝ) := by
        rw [show pairs.filter pred = big by rfl, hbig_card]
      linarith

/-- Arithmetic separation used in the coarse C.2 count: the main
trivial-trivial term dominates the overcounted character-sum remainder when
`q ≥ 5`. -/
public theorem CFSG.appendixC_lemma_C_2_coarse_count_arithmetic
    [Fact q.Prime] (hoddp : Odd p) (hoddq : Odd q) (hq5 : 5 ≤ q) :
    2 * ((p - 1) * (p - 1)) + 2 +
        (p - 2) * (p - 3) * p ^ (q / 2 + 1) < p ^ q := by
  have hp : Nat.Prime p := Fact.out
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    rcases hoddp with ⟨k, hk⟩
    omega
  have hp_pos : 0 < p := hp.pos
  have hqsub_ge_two : 2 ≤ q - 2 := by omega
  have hqexp : q / 2 + 1 ≤ q - 2 := by
    rcases hoddq with ⟨k, hk⟩
    rw [hk]
    omega
  have hpow_exp :
      p ^ (q / 2 + 1) ≤ p ^ (q - 2) :=
    Nat.pow_le_pow_right hp_pos hqexp
  have hsmall :
      2 * ((p - 1) * (p - 1)) + 2 ≤ 2 * p ^ (q - 2) := by
    have hbase : 2 * ((p - 1) * (p - 1)) + 2 ≤ 2 * (p * p) := by
      rcases Nat.exists_eq_add_of_le hp3 with ⟨k, rfl⟩
      have hk1 : 3 + k - 1 = k + 2 := by omega
      rw [hk1]
      nlinarith [Nat.zero_le k]
    have hp2pow : p * p ≤ p ^ (q - 2) := by
      calc
        p * p = p ^ 2 := by ring
        _ ≤ p ^ (q - 2) := Nat.pow_le_pow_right hp_pos hqsub_ge_two
    exact hbase.trans (Nat.mul_le_mul_left 2 hp2pow)
  have hbig :
      (p - 2) * (p - 3) * p ^ (q / 2 + 1) ≤
        (p - 2) * (p - 3) * p ^ (q - 2) := by
    exact Nat.mul_le_mul_left ((p - 2) * (p - 3)) hpow_exp
  have hcoeff : 2 + (p - 2) * (p - 3) < p * p := by
    rcases Nat.exists_eq_add_of_le hp3 with ⟨k, rfl⟩
    have hk2 : 3 + k - 2 = k + 1 := by omega
    have hk3 : 3 + k - 3 = k := by omega
    rw [hk2, hk3]
    nlinarith [Nat.zero_le k]
  have hcombined :
      2 * p ^ (q - 2) + (p - 2) * (p - 3) * p ^ (q - 2) <
        p * p * p ^ (q - 2) := by
    have hpow_pos : 0 < p ^ (q - 2) := pow_pos hp_pos _
    calc
      2 * p ^ (q - 2) + (p - 2) * (p - 3) * p ^ (q - 2) =
          (2 + (p - 2) * (p - 3)) * p ^ (q - 2) := by ring
      _ < (p * p) * p ^ (q - 2) :=
          Nat.mul_lt_mul_of_pos_right hcoeff hpow_pos
  have hto :
      2 * ((p - 1) * (p - 1)) + 2 +
          (p - 2) * (p - 3) * p ^ (q / 2 + 1) ≤
        2 * p ^ (q - 2) + (p - 2) * (p - 3) * p ^ (q - 2) :=
    Nat.add_le_add hsmall hbig
  have htarget :
      p * p * p ^ (q - 2) = p ^ q := by
    calc
      p * p * p ^ (q - 2) = p ^ 2 * p ^ (q - 2) := by ring
      _ = p ^ (2 + (q - 2)) := by rw [← pow_add]
      _ = p ^ q := by congr; omega
  exact hto.trans_lt (by simpa [htarget] using hcombined)

/-- Summing all complex norm characters gives the indicator of the norm-one
condition. This is the local Fourier-orthogonality step behind the source
character count in Appendix C Lemma C.2. -/
public theorem CFSG.appendixC_norm_character_sum_indicator
    [Fact q.Prime] [Fintype ((ZMod p)ˣ →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod p)ˣ)]
    (z : appendixCField p q) :
    (∑ χ : (ZMod p)ˣ →* ℂˣ, appendixCNormCharacter p q χ z) =
      if (Algebra.norm (ZMod p) (S := appendixCField p q)) z = 1 then
        (Nat.card (ZMod p)ˣ : ℂ) else 0 := by
  classical
  by_cases hz : z = 0
  · subst z
    have hnorm0 :
        (Algebra.norm (ZMod p) (S := appendixCField p q))
          (0 : appendixCField p q) ≠ 1 := by
      simp
    rw [if_neg hnorm0]
    apply Finset.sum_eq_zero
    intro χ _hχ
    simp [appendixCNormCharacter, MulChar.map_nonunit]
  · have hnorm_ne :
        (Algebra.norm (ZMod p) (S := appendixCField p q)) z ≠ 0 := by
      simpa [Algebra.norm_eq_zero_iff] using hz
    let nz : (ZMod p)ˣ :=
      Units.mk0 ((Algebra.norm (ZMod p) (S := appendixCField p q)) z) hnorm_ne
    have hsum := appendixC_finite_abelian_character_sum_apply (Q := (ZMod p)ˣ) nz
    have hpoint : ∀ χ : (ZMod p)ˣ →* ℂˣ,
        appendixCNormCharacter p q χ z = (χ nz : ℂ) := by
      intro χ
      change (MulChar.ofUnitHom
          (χ.comp (Units.map (Algebra.norm (ZMod p) (S := appendixCField p q))))
            ((Units.mk0 z hz : (appendixCField p q)ˣ) : appendixCField p q)) = _
      rw [MulChar.ofUnitHom_coe]
      have hunit :
          (Units.map (Algebra.norm (ZMod p) (S := appendixCField p q))) (Units.mk0 z hz) =
            nz := by
        ext
        rfl
      simp [MonoidHom.comp_apply, hunit]
    calc
      (∑ χ : (ZMod p)ˣ →* ℂˣ, appendixCNormCharacter p q χ z) =
          ∑ χ : (ZMod p)ˣ →* ℂˣ, (χ nz : ℂ) := by
            apply Finset.sum_congr rfl
            intro χ _hχ
            exact hpoint χ
      _ = (if nz = 1 then (Nat.card (ZMod p)ˣ : ℂ) else 0) := hsum
      _ = (if (Algebra.norm (ZMod p) (S := appendixCField p q)) z = 1 then
            (Nat.card (ZMod p)ˣ : ℂ) else 0) := by
            by_cases hn1 :
                (Algebra.norm (ZMod p) (S := appendixCField p q)) z = 1
            · have hnz1 : nz = 1 := by
                ext
                exact hn1
              simp [hn1, hnz1]
            · have hnz1 : nz ≠ 1 := by
                intro h
                apply hn1
                exact Units.ext_iff.mp h
              simp [hn1, hnz1]

/-- Exact character-sum formula for the Appendix C set `E`: the double norm
character sum counts the pairs `u + v = 2`, hence `|E|`. The remaining source
C.2 debt is to estimate the nontrivial character contribution. -/
public theorem CFSG.appendixCE_character_sum_formula
    [Fact q.Prime] [Fintype (appendixCField p q)] [Fintype (appendixCE p q)]
    [Fintype ((ZMod p)ˣ →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod p)ˣ)] :
    (∑ χ : (ZMod p)ˣ →* ℂˣ, ∑ ψ : (ZMod p)ˣ →* ℂˣ,
      ∑ z : appendixCField p q,
        appendixCNormCharacter p q χ z *
          appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) =
      (Nat.card (ZMod p)ˣ : ℂ) * (Nat.card (ZMod p)ˣ : ℂ) *
        (Nat.card (appendixCE p q) : ℂ) := by
  classical
  let N : ℂ := Nat.card (ZMod p)ˣ
  have hrearrange :
      (∑ χ : (ZMod p)ˣ →* ℂˣ, ∑ ψ : (ZMod p)ˣ →* ℂˣ,
        ∑ z : appendixCField p q,
          appendixCNormCharacter p q χ z *
            appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) =
        ∑ z : appendixCField p q,
          (∑ χ : (ZMod p)ˣ →* ℂˣ, appendixCNormCharacter p q χ z) *
          (∑ ψ : (ZMod p)ˣ →* ℂˣ,
            appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) := by
    calc
      (∑ χ : (ZMod p)ˣ →* ℂˣ, ∑ ψ : (ZMod p)ˣ →* ℂˣ,
        ∑ z : appendixCField p q,
          appendixCNormCharacter p q χ z *
            appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) =
          ∑ z : appendixCField p q, ∑ χ : (ZMod p)ˣ →* ℂˣ,
            ∑ ψ : (ZMod p)ˣ →* ℂˣ,
              appendixCNormCharacter p q χ z *
                appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z) := by
            calc
              (∑ χ : (ZMod p)ˣ →* ℂˣ, ∑ ψ : (ZMod p)ˣ →* ℂˣ,
                ∑ z : appendixCField p q,
                  appendixCNormCharacter p q χ z *
                    appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) =
                  ∑ χ : (ZMod p)ˣ →* ℂˣ, ∑ z : appendixCField p q,
                    ∑ ψ : (ZMod p)ˣ →* ℂˣ,
                      appendixCNormCharacter p q χ z *
                        appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z) := by
                    apply Finset.sum_congr rfl
                    intro χ _hχ
                    rw [Finset.sum_comm]
              _ = ∑ z : appendixCField p q, ∑ χ : (ZMod p)ˣ →* ℂˣ,
                    ∑ ψ : (ZMod p)ˣ →* ℂˣ,
                      appendixCNormCharacter p q χ z *
                        appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z) := by
                    rw [Finset.sum_comm]
      _ = ∑ z : appendixCField p q,
          (∑ χ : (ZMod p)ˣ →* ℂˣ, appendixCNormCharacter p q χ z) *
          (∑ ψ : (ZMod p)ˣ →* ℂˣ,
            appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) := by
            apply Finset.sum_congr rfl
            intro z _hz
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro χ _hχ
            rw [Finset.mul_sum]
  calc
    (∑ χ : (ZMod p)ˣ →* ℂˣ, ∑ ψ : (ZMod p)ˣ →* ℂˣ,
      ∑ z : appendixCField p q,
        appendixCNormCharacter p q χ z *
          appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) =
        ∑ z : appendixCField p q,
          (∑ χ : (ZMod p)ˣ →* ℂˣ, appendixCNormCharacter p q χ z) *
          (∑ ψ : (ZMod p)ˣ →* ℂˣ,
            appendixCNormCharacter p q ψ ((2 : appendixCField p q) - z)) := hrearrange
    _ = ∑ z : appendixCField p q,
          (if (Algebra.norm (ZMod p) (S := appendixCField p q)) z = 1 then N else 0) *
          (if (Algebra.norm (ZMod p) (S := appendixCField p q))
              ((2 : appendixCField p q) - z) = 1 then N else 0) := by
            apply Finset.sum_congr rfl
            intro z _hz
            rw [appendixC_norm_character_sum_indicator (p := p) (q := q) z,
              appendixC_norm_character_sum_indicator (p := p) (q := q)
                ((2 : appendixCField p q) - z)]
    _ = ∑ z : appendixCField p q,
          if z ∈ appendixCE p q then N * N else 0 := by
            apply Finset.sum_congr rfl
            intro z _hz
            by_cases h1 :
                (Algebra.norm (ZMod p) (S := appendixCField p q)) z = 1 <;>
            by_cases h2 :
                (Algebra.norm (ZMod p) (S := appendixCField p q))
                  ((2 : appendixCField p q) - z) = 1 <;>
            simp [appendixCE, h1, h2]
    _ = (Nat.card (ZMod p)ˣ : ℂ) * (Nat.card (ZMod p)ˣ : ℂ) *
        (Nat.card (appendixCE p q) : ℂ) := by
            rw [← Finset.sum_filter]
            simp only [Finset.sum_const, nsmul_eq_mul]
            rw [mul_comm]
            congr 1
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The action of the norm-one subgroup `U` on the additive group `P`. -/
@[expose] public def CFSG.appendixCAction :
    appendixCNormOneUnits p q →* MulAut (appendixCP p q) :=
  (appendixCUnitAction p q).comp (appendixCNormOneUnits p q).subtype

/-- The Appendix C action is multiplication by the underlying field unit. -/
public theorem CFSG.appendixCAction_apply_toAdd
    (u : appendixCNormOneUnits p q) (x : appendixCP p q) :
    Multiplicative.toAdd ((appendixCAction p q u) x) =
      (u : (appendixCField p q)ˣ) * Multiplicative.toAdd x := by
  rfl


/-- The semidirect product `H = PU` from Theorem C. -/
public abbrev CFSG.appendixCH : Type :=
  appendixCP p q ⋊[appendixCAction p q] appendixCNormOneUnits p q

/-- The Appendix C semidirect product is finite. -/
public instance CFSG.appendixCH_finite : Finite (appendixCH p q) :=
  Finite.of_equiv (appendixCP p q × appendixCNormOneUnits p q)
    (SemidirectProduct.equivProd (φ := appendixCAction p q)).symm

/-- The subgroup `P` of `H = PU`. -/
@[expose] public def CFSG.appendixCPInH : Subgroup (appendixCH p q) :=
  MonoidHom.range SemidirectProduct.inl

/-- Membership in `P ≤ H`, unfolded through the left injection into the
semidirect product. -/
public theorem CFSG.appendixCPInH_mem_iff
    (x : appendixCH p q) :
    x ∈ appendixCPInH p q ↔ ∃ z : appendixCP p q, x = SemidirectProduct.inl z := by
  rw [appendixCPInH]
  constructor
  · intro hx
    rcases hx with ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩

/-- In the Appendix C semidirect product, `P` is normal. -/
public instance CFSG.appendixCPInH_normal : (appendixCPInH p q).Normal := by
  have hker : (SemidirectProduct.inl : appendixCP p q →* appendixCH p q).range =
      (SemidirectProduct.rightHom : appendixCH p q →* appendixCNormOneUnits p q).ker := by
    exact SemidirectProduct.range_inl_eq_ker_rightHom
  rw [appendixCPInH, hker]
  infer_instance

/-- The image in `P` of the additive group of `F_p`. -/
@[expose] public def CFSG.appendixCP0InP : Subgroup (appendixCP p q) :=
  MonoidHom.range (AddMonoidHom.toMultiplicative
    (algebraMap (ZMod p) (appendixCField p q)).toAddMonoidHom)

/-- Membership in the prime-field subgroup `P_0`, unfolded through the
algebra map. -/
public theorem CFSG.appendixCP0InP_mem_iff
    (x : appendixCP p q) :
    x ∈ appendixCP0InP p q ↔
      ∃ c : ZMod p,
        x = Multiplicative.ofAdd
          (algebraMap (ZMod p) (appendixCField p q) c) := by
  rw [appendixCP0InP]
  constructor
  · intro hx
    rcases hx with ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

/-- The subgroup `P_0` of `H`. -/
@[expose] public def CFSG.appendixCP0InH : Subgroup (appendixCH p q) :=
  Subgroup.map SemidirectProduct.inl (appendixCP0InP p q)

/-- Membership in `P_0 ≤ H`, unfolded through the prime-field embedding into
the semidirect product. -/
public theorem CFSG.appendixCP0InH_mem_iff
    (x : appendixCH p q) :
    x ∈ appendixCP0InH p q ↔
      ∃ c : ZMod p,
        x = SemidirectProduct.inl (Multiplicative.ofAdd
          (algebraMap (ZMod p) (appendixCField p q) c)) := by
  rw [appendixCP0InH]
  constructor
  · intro hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [appendixCP0InP] at hz
    rcases hz with ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c), ?_, rfl⟩
    rw [appendixCP0InP]
    exact ⟨c, rfl⟩

/-- The subgroup `U` of `H`. -/
@[expose] public def CFSG.appendixCUInH : Subgroup (appendixCH p q) :=
  MonoidHom.range SemidirectProduct.inr

/-- Membership in `U ≤ H`, unfolded through the right injection into the
semidirect product. -/
public theorem CFSG.appendixCUInH_mem_iff
    (x : appendixCH p q) :
    x ∈ appendixCUInH p q ↔
      ∃ u : appendixCNormOneUnits p q, x = SemidirectProduct.inr u := by
  rw [appendixCUInH]
  constructor
  · intro hx
    rcases hx with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩

/-- The prime-field subgroup `P0` is contained in `P`. -/
public theorem CFSG.appendixCP0InH_le_appendixCPInH :
    appendixCP0InH p q ≤ appendixCPInH p q := by
  intro x hx
  rcases (appendixCP0InH_mem_iff (p := p) (q := q) x).1 hx with ⟨c, rfl⟩
  exact (appendixCPInH_mem_iff (p := p) (q := q) _).2
    ⟨Multiplicative.ofAdd (algebraMap (ZMod p) (appendixCField p q) c), rfl⟩


/-- The subgroups `P` and `U` generate the semidirect product `H = PU`. -/
public theorem CFSG.appendixCPInH_sup_appendixCUInH_eq_top :
    appendixCPInH p q ⊔ appendixCUInH p q = ⊤ := by
  apply eq_top_iff.mpr
  intro x _hx
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact (appendixCPInH p q ⊔ appendixCUInH p q).mul_mem
    (Subgroup.mem_sup_left ((appendixCPInH_mem_iff (p := p) (q := q) _).2
      ⟨x.left, rfl⟩))
    (Subgroup.mem_sup_right ((appendixCUInH_mem_iff (p := p) (q := q) _).2
      ⟨x.right, rfl⟩))

/-- Every element of `H = PU` has a `P * U` decomposition. -/
public theorem CFSG.appendixCH_exists_P_U_decomposition (x : appendixCH p q) :
    ∃ s : appendixCH p q, s ∈ appendixCPInH p q ∧
      ∃ u : appendixCH p q, u ∈ appendixCUInH p q ∧ x = s * u := by
  refine ⟨SemidirectProduct.inl x.left, ?_, SemidirectProduct.inr x.right, ?_, ?_⟩
  · exact (appendixCPInH_mem_iff (p := p) (q := q) _).2 ⟨x.left, rfl⟩
  · exact (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨x.right, rfl⟩
  · exact (SemidirectProduct.inl_left_mul_inr_right x).symm


/-- The embedded images of `P` and `U` generate the embedded image of `H`. -/
public theorem CFSG.appendixCEmbedding_CPInH_sup_CUInH_eq_image_top
    {G : Type u} [Group G] (σ : appendixCH p q →* G) :
    Subgroup.map σ (appendixCPInH p q) ⊔
      Subgroup.map σ (appendixCUInH p q) =
        Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) := by
  rw [← Subgroup.map_sup, appendixCPInH_sup_appendixCUInH_eq_top]

/-- Every element of the embedded image of `H = PU` has an embedded `P * U`
decomposition. -/
public theorem CFSG.appendixCEmbedding_exists_P_U_decomposition
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {x : G} (hx : x ∈ Subgroup.map σ (⊤ : Subgroup (appendixCH p q))) :
    ∃ s : G, s ∈ Subgroup.map σ (appendixCPInH p q) ∧
      ∃ u : G, u ∈ Subgroup.map σ (appendixCUInH p q) ∧ x = s * u := by
  rcases hx with ⟨xH, _hxH, rfl⟩
  rcases appendixCH_exists_P_U_decomposition (p := p) (q := q) xH with
    ⟨sH, hsH, uH, huH, hxH⟩
  refine ⟨σ sH, ⟨sH, hsH, rfl⟩, σ uH, ⟨uH, huH, rfl⟩, ?_⟩
  rw [hxH]
  simp [map_mul]

/-- Appendix C Lemma C.3, Step 1: every element of `PU` has a decomposition
`u * s * v` with `u, v ∈ U` and `s ∈ P0`. -/
public theorem CFSG.appendixCH_exists_U_P0_U_decomposition
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (x : appendixCH p q) :
    ∃ (u v : appendixCNormOneUnits p q) (s : appendixCP0InH p q),
      x = SemidirectProduct.inr u * (s : appendixCH p q) *
        SemidirectProduct.inr v := by
  by_cases hx0 : Multiplicative.toAdd x.left = (0 : appendixCField p q)
  · refine ⟨1, x.right, 1, ?_⟩
    ext <;> simp [hx0]
  · let z : (appendixCField p q)ˣ :=
      Units.mk0 (Multiplicative.toAdd x.left) hx0
    rcases appendixCFieldUnit_eq_primeField_mul_normOneUnit
        (p := p) (q := q) hA z with
      ⟨c, u, hz⟩
    let v : appendixCNormOneUnits p q := u⁻¹ * x.right
    let sH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) (c : ZMod p)))
    have hsH : sH ∈ appendixCP0InH p q := by
      rw [appendixCP0InH_mem_iff]
      exact ⟨c, rfl⟩
    refine ⟨u, v, ⟨sH, hsH⟩, ?_⟩
    ext
    · simp [sH, appendixCAction_apply_toAdd]
      dsimp [z] at hz
      simpa [mul_comm] using hz
    · simp [sH, v, mul_assoc]

/-- Appendix C Lemma C.3, Step 2, in prime-field coordinates. If
`s_1, s_2 in P_0`, `u in U`, and `s_1 u s_2` lies in `U`, then either
both prime-field terms are trivial, or the `U`-term is trivial and
`s_1 s_2 = 1`. -/
public theorem CFSG.appendixCP0_mul_U_mul_P0_mem_U_core
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (u : appendixCNormOneUnits p q)
    (c1 c2 : ZMod p)
    (hmem : ((SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) c1)) : appendixCH p q) *
      SemidirectProduct.inr u *
      SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) c2)) ∈
        appendixCUInH p q)) :
    ((SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) c1)) : appendixCH p q) = 1 ∧
      (SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) c2)) : appendixCH p q) = 1) ∨
    (u = 1 ∧
      (SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) c1)) : appendixCH p q) *
      SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) c2)) = 1) := by
  have hleft : algebraMap (ZMod p) (appendixCField p q) c1 +
      (u : (appendixCField p q)ˣ) *
        algebraMap (ZMod p) (appendixCField p q) c2 = 0 := by
    rw [appendixCUInH_mem_iff] at hmem
    rcases hmem with ⟨v, hv⟩
    have hleft := congrArg SemidirectProduct.left hv
    simpa [appendixCAction_apply_toAdd] using
      congrArg Multiplicative.toAdd hleft
  by_cases hc1 : c1 = 0
  · left
    constructor
    · simp [hc1]
    · have hc2map : algebraMap (ZMod p) (appendixCField p q) c2 = 0 := by
        have hmul : ((u : (appendixCField p q)ˣ) : appendixCField p q) *
            algebraMap (ZMod p) (appendixCField p q) c2 = 0 := by
          simpa [hc1] using hleft
        exact eq_zero_of_ne_zero_of_mul_left_eq_zero
          (Units.ne_zero (u : (appendixCField p q)ˣ)) hmul
      have hc2 : c2 = 0 := by
        exact FaithfulSMul.algebraMap_injective (ZMod p) (appendixCField p q)
          (by simpa using hc2map)
      simp [hc2]
  · right
    have hc2 : c2 ≠ 0 := by
      intro hc2
      have hc1map : algebraMap (ZMod p) (appendixCField p q) c1 = 0 := by
        simpa [hc2] using hleft
      exact hc1 (FaithfulSMul.algebraMap_injective (ZMod p) (appendixCField p q)
        (by simpa using hc1map))
    have hu_prime : ((u : (appendixCField p q)ˣ) : appendixCField p q) =
        algebraMap (ZMod p) (appendixCField p q) (-c1 / c2) := by
      have hc2map : algebraMap (ZMod p) (appendixCField p q) c2 ≠ 0 := by
        exact (map_ne_zero (algebraMap (ZMod p) (appendixCField p q))).2 hc2
      rw [map_div₀, map_neg]
      field_simp [hc2map]
      linear_combination hleft
    have hu1 : u = 1 :=
      appendixCNormOneUnits_eq_one_of_coe_algebraMap (p := p) (q := q)
        hA u hu_prime
    constructor
    · exact hu1
    · have hc12map : algebraMap (ZMod p) (appendixCField p q) (c1 + c2) = 0 := by
        rw [map_add]
        simpa [hu1] using hleft
      have hc12 : c1 + c2 = 0 := by
        exact FaithfulSMul.algebraMap_injective (ZMod p) (appendixCField p q)
          (by simpa using hc12map)
      ext <;> simp [← map_add, hc12]

/-- Appendix C Lemma C.3, Step 2, stated for arbitrary elements of `P_0`. -/
public theorem CFSG.appendixCP0_mul_U_mul_P0_mem_U_cases
    [Fact q.Prime]
    (hA : appendixCConditionA p q) {s1 s2 : appendixCH p q}
    (hs1 : s1 ∈ appendixCP0InH p q) (hs2 : s2 ∈ appendixCP0InH p q)
    (u : appendixCNormOneUnits p q)
    (hmem : s1 * SemidirectProduct.inr u * s2 ∈ appendixCUInH p q) :
    (s1 = 1 ∧ s2 = 1) ∨ (u = 1 ∧ s1 * s2 = 1) := by
  rw [appendixCP0InH_mem_iff] at hs1 hs2
  rcases hs1 with ⟨c1, rfl⟩
  rcases hs2 with ⟨c2, rfl⟩
  exact appendixCP0_mul_U_mul_P0_mem_U_core (p := p) (q := q) hA u c1 c2
    hmem

/-- Embedded form of Appendix C Lemma C.3, Step 1. Every element in the image
of `PU` has a `U-P0-U` decomposition in the ambient group. -/
public theorem CFSG.appendixCEmbedding_exists_U_P0_U_decomposition
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    {x : G} (hx : x ∈ Subgroup.map σ (⊤ : Subgroup (appendixCH p q))) :
    ∃ u : G, u ∈ Subgroup.map σ (appendixCUInH p q) ∧
      ∃ s : G, s ∈ Subgroup.map σ (appendixCP0InH p q) ∧
        ∃ v : G, v ∈ Subgroup.map σ (appendixCUInH p q) ∧
          x = u * s * v := by
  rcases hx with ⟨xH, _hxH, rfl⟩
  rcases appendixCH_exists_U_P0_U_decomposition (p := p) (q := q) hA xH with
    ⟨u, v, s, hxH⟩
  refine ⟨σ (SemidirectProduct.inr u), ?_, σ (s : appendixCH p q), ?_,
    σ (SemidirectProduct.inr v), ?_, ?_⟩
  · exact ⟨SemidirectProduct.inr u,
      (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨u, rfl⟩, rfl⟩
  · exact ⟨s, s.property, rfl⟩
  · exact ⟨SemidirectProduct.inr v,
      (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨v, rfl⟩, rfl⟩
  · rw [hxH]
    simp [map_mul]

/-- Embedded form of Appendix C Lemma C.3, Step 2. The `P0-U-P0` alternative
survives passage through an injective ambient embedding. -/
public theorem CFSG.appendixCEmbedding_P0_mul_U_mul_P0_mem_U_cases
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {s1 s2 u : G}
    (hs1 : s1 ∈ Subgroup.map σ (appendixCP0InH p q))
    (hs2 : s2 ∈ Subgroup.map σ (appendixCP0InH p q))
    (hu : u ∈ Subgroup.map σ (appendixCUInH p q))
    (hmem : s1 * u * s2 ∈ Subgroup.map σ (appendixCUInH p q)) :
    (s1 = 1 ∧ s2 = 1) ∨ (u = 1 ∧ s1 * s2 = 1) := by
  rcases hs1 with ⟨s1H, hs1H, rfl⟩
  rcases hs2 with ⟨s2H, hs2H, rfl⟩
  rcases hu with ⟨uH, huH, rfl⟩
  rcases (appendixCUInH_mem_iff (p := p) (q := q) uH).1 huH with
    ⟨u0, rfl⟩
  rcases hmem with ⟨wH, hwH, hwH_eq⟩
  have hpre : s1H * SemidirectProduct.inr u0 * s2H = wH := by
    apply hσ
    simpa [map_mul, mul_assoc] using hwH_eq.symm
  have hmemH : s1H * SemidirectProduct.inr u0 * s2H ∈ appendixCUInH p q := by
    simpa [hpre] using hwH
  rcases appendixCP0_mul_U_mul_P0_mem_U_cases (p := p) (q := q) hA
      hs1H hs2H u0 hmemH with
    htrivial | hunit
  · rcases htrivial with ⟨hs1_one, hs2_one⟩
    left
    constructor <;> simp [hs1_one, hs2_one]
  · rcases hunit with ⟨hu_one, hs12_one⟩
    right
    constructor
    · simp [hu_one]
    · simpa [map_mul] using congrArg σ hs12_one


/-- Forward field-coordinate calculation for Appendix C C.3, Step 4. If two
norm-one units have underlying field values summing to `2`, then for every
prime-field element `s` the semidirect-product equation `s^2 = s^v s^z` holds. -/
public theorem CFSG.appendixCP0_conj_normOneUnits_sq_eq_mul_of_add_eq_two
    {c : ZMod p} (v z : appendixCNormOneUnits p q)
    (hadd :
      (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2) :
    ((SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c)) : appendixCH p q) ^ 2) =
      ((SemidirectProduct.inr v : appendixCH p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd
            (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q) *
          (SemidirectProduct.inr v : appendixCH p q)⁻¹) *
        ((SemidirectProduct.inr z : appendixCH p q) *
          SemidirectProduct.inl (Multiplicative.ofAdd
            (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q) *
          (SemidirectProduct.inr z : appendixCH p q)⁻¹) := by
  ext
  · simp [pow_two, appendixCAction_apply_toAdd]
    calc
      (algebraMap (ZMod p) (appendixCField p q)) c +
          (algebraMap (ZMod p) (appendixCField p q)) c =
          (2 : appendixCField p q) *
            (algebraMap (ZMod p) (appendixCField p q)) c := by ring
      _ = ((((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
              appendixCField p q) +
            (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
              appendixCField p q)) *
            (algebraMap (ZMod p) (appendixCField p q)) c := by rw [hadd]
      _ = (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
              appendixCField p q) *
            (algebraMap (ZMod p) (appendixCField p q)) c +
          (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
              appendixCField p q) *
            (algebraMap (ZMod p) (appendixCField p q)) c := by ring
  · simp [pow_two]

/-- The first C5 equation at the endpoint `s₁ = s⁻¹`, read in Lean's
semidirect-product convention, gives the inverse value identity
`v⁻¹ + z⁻¹ = 2`. This is the explicit action-convention form needed before
translating the source's final `v + z = 2` endpoint. -/
public theorem CFSG.appendixCP0_conj_normOneUnits_inv_add_inv_eq_two_of_C5
    {c : ZMod p} (hc : c ≠ 0) (z u v : appendixCNormOneUnits p q)
    (h :
      (SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q) :
          appendixCH p q) *
        (SemidirectProduct.inr z : appendixCH p q) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd
          (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q) :
          appendixCH p q) ^ (-2 : ℤ)) =
      (SemidirectProduct.inr u : appendixCH p q) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd
          (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q) :
          appendixCH p q)⁻¹) *
        (SemidirectProduct.inr v : appendixCH p q)) :
    (((v⁻¹ : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
        appendixCField p q) +
      (((z⁻¹ : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
        appendixCField p q) = 2 := by
  have hleft := congrArg SemidirectProduct.left h
  have htoAdd := congrArg Multiplicative.toAdd hleft
  have hright := congrArg SemidirectProduct.right h
  simp [appendixCAction_apply_toAdd, zpow_ofNat, pow_two, mul_assoc] at htoAdd hright
  have hprod : z = u * v := by
    simpa using hright
  subst z
  have hcmap : algebraMap (ZMod p) (appendixCField p q) c ≠ 0 := by
    exact (map_ne_zero (algebraMap (ZMod p) (appendixCField p q))).2 hc
  field_simp [hcmap] at htoAdd
  ring_nf at htoAdd
  have hcoord :
      (1 : appendixCField p q) -
          (((u : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) *
          (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) * 2 =
        -(((u : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) := by
    simpa [mul_assoc] using htoAdd
  have hsum :
      (((u : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) + 1 =
        (((u : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) *
          (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) * 2 := by
    linear_combination hcoord
  change (((((v : (appendixCField p q)ˣ)⁻¹) : (appendixCField p q)ˣ) :
        appendixCField p q)) +
      ((((((u : (appendixCField p q)ˣ) * (v : (appendixCField p q)ˣ))⁻¹) :
        (appendixCField p q)ˣ) : appendixCField p q)) = 2
  simp only [Units.val_inv_eq_inv_val, Units.val_mul]
  have hu0 : (((u : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
      appendixCField p q) ≠ 0 := Units.ne_zero _
  have hv0 : (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
      appendixCField p q) ≠ 0 := Units.ne_zero _
  field_simp [hu0, hv0]
  simpa [mul_comm, mul_assoc, mul_left_comm] using hsum

/-- Embedded form of
`appendixCP0_conj_normOneUnits_inv_add_inv_eq_two_of_C5`. -/
public theorem CFSG.appendixCEmbedding_CP0_conj_normOneUnits_inv_add_inv_eq_two_of_C5
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {c : ZMod p} (hc : c ≠ 0) {s uimg vimg : G}
    {z u0 v0 : appendixCNormOneUnits p q}
    (hs : s = σ (SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)))
    (hu : uimg = σ (SemidirectProduct.inr u0))
    (hv : vimg = σ (SemidirectProduct.inr v0))
    (h : s * σ (SemidirectProduct.inr z) * s ^ (-2 : ℤ) =
      uimg * s⁻¹ * vimg) :
    (((v0⁻¹ : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
        appendixCField p q) +
      (((z⁻¹ : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
        appendixCField p q) = 2 := by
  subst s
  subst uimg
  subst vimg
  exact appendixCP0_conj_normOneUnits_inv_add_inv_eq_two_of_C5
    (p := p) (q := q) hc z u0 v0 (by
      apply hσ
      simpa [map_mul, map_inv, map_zpow] using h)

/-- Embedded version of the forward C2 field-coordinate calculation. -/
public theorem CFSG.appendixCEmbedding_CP0_conj_normOneUnits_sq_eq_mul_of_add_eq_two
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {c : ZMod p} (v z : appendixCNormOneUnits p q)
    (hadd :
      (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2) :
    (σ (SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)) ^ 2) =
      (σ (SemidirectProduct.inr v) *
          σ (SemidirectProduct.inl (Multiplicative.ofAdd
            (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)) *
          (σ (SemidirectProduct.inr v))⁻¹) *
        (σ (SemidirectProduct.inr z) *
          σ (SemidirectProduct.inl (Multiplicative.ofAdd
            (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)) *
          (σ (SemidirectProduct.inr z))⁻¹) := by
  simpa [map_mul, map_inv, map_pow] using congrArg σ
    (appendixCP0_conj_normOneUnits_sq_eq_mul_of_add_eq_two
      (p := p) (q := q) (c := c) v z hadd)

/-- Three-factor product form of the forward C2 calculation. This is the
orientation obtained by expanding
`s ^ 2 = (v * s * v⁻¹) * (z * s * z⁻¹)` into a product whose `U` factors are
`v`, `v⁻¹ * z`, and `z⁻¹`. -/
public theorem CFSG.appendixCP0_conj_normOneUnits_C2_product_of_add_eq_two
    {c : ZMod p} (v z : appendixCNormOneUnits p q)
    (hadd :
      (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2) :
    let sH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)
    sH ^ (-2 : ℤ) *
      (SemidirectProduct.inr v : appendixCH p q) * sH *
      (SemidirectProduct.inr (v⁻¹ * z) : appendixCH p q) * sH *
      (SemidirectProduct.inr z⁻¹ : appendixCH p q) = 1 := by
  dsimp only
  let sH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd
    (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)
  have hsq : sH ^ 2 =
      ((SemidirectProduct.inr v : appendixCH p q) * sH *
          (SemidirectProduct.inr v : appendixCH p q)⁻¹) *
        ((SemidirectProduct.inr z : appendixCH p q) * sH *
          (SemidirectProduct.inr z : appendixCH p q)⁻¹) := by
    simpa [sH] using appendixCP0_conj_normOneUnits_sq_eq_mul_of_add_eq_two
      (p := p) (q := q) (c := c) v z hadd
  have hprod :
      sH ^ (-2 : ℤ) *
        (((SemidirectProduct.inr v : appendixCH p q) * sH *
            (SemidirectProduct.inr v : appendixCH p q)⁻¹) *
          ((SemidirectProduct.inr z : appendixCH p q) * sH *
            (SemidirectProduct.inr z : appendixCH p q)⁻¹)) = 1 := by
    rw [← hsq]
    simp [zpow_neg, zpow_ofNat, pow_two]
  change sH ^ (-2 : ℤ) *
      (SemidirectProduct.inr v : appendixCH p q) * sH *
      (SemidirectProduct.inr (v⁻¹ * z) : appendixCH p q) * sH *
      (SemidirectProduct.inr z⁻¹ : appendixCH p q) = 1
  simpa [sH, map_mul, map_inv, mul_assoc] using hprod

/-- Embedded version of the three-factor C2 product calculation. -/
public theorem CFSG.appendixCEmbedding_CP0_conj_normOneUnits_C2_product_of_add_eq_two
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {c : ZMod p} (v z : appendixCNormOneUnits p q)
    (hadd :
      (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2) :
    let sH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)
    (σ sH) ^ (-2 : ℤ) *
      σ (SemidirectProduct.inr v) * σ sH *
      σ (SemidirectProduct.inr (v⁻¹ * z)) * σ sH *
      σ (SemidirectProduct.inr z⁻¹) = 1 := by
  dsimp only
  let sH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd
    (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)
  have hsrc :
      sH ^ (-2 : ℤ) *
        (SemidirectProduct.inr v : appendixCH p q) * sH *
        (SemidirectProduct.inr (v⁻¹ * z) : appendixCH p q) * sH *
        (SemidirectProduct.inr z⁻¹ : appendixCH p q) = 1 := by
    simpa [sH] using
      appendixCP0_conj_normOneUnits_C2_product_of_add_eq_two
        (p := p) (q := q) (c := c) v z hadd
  simpa [sH, map_mul, map_zpow] using congrArg σ hsrc

/-- Cyclically rotated three-factor product form of the forward C2 calculation.
This is the orientation used in C.3 Step 4 when the desired first C5 factor is
the inverse of the second summand. Starting from the product with factors
`v`, `v⁻¹ * z`, and `z⁻¹`, rotate the last `s * z⁻¹` block to the front. -/
public theorem CFSG.appendixCP0_conj_normOneUnits_C2_cyclic_product_of_add_eq_two
    {c : ZMod p} (v z : appendixCNormOneUnits p q)
    (hadd :
      (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2) :
    let sH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)
    sH * (SemidirectProduct.inr z⁻¹ : appendixCH p q) * sH ^ (-2 : ℤ) *
      (SemidirectProduct.inr v : appendixCH p q) * sH *
      (SemidirectProduct.inr (v⁻¹ * z) : appendixCH p q) = 1 := by
  dsimp only
  let sH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd
    (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)
  let A : appendixCH p q := sH ^ (-2 : ℤ)
  let B : appendixCH p q := SemidirectProduct.inr v
  let C : appendixCH p q := sH
  let D : appendixCH p q := SemidirectProduct.inr (v⁻¹ * z)
  let E : appendixCH p q := sH
  let F : appendixCH p q := SemidirectProduct.inr z⁻¹
  have hprod : A * B * C * D * E * F = 1 := by
    simpa [A, B, C, D, E, F, sH] using
      appendixCP0_conj_normOneUnits_C2_product_of_add_eq_two
        (p := p) (q := q) (c := c) v z hadd
  have hrot : E * F * A * B * C * D = 1 := by
    have h := congrArg (fun g : appendixCH p q => (E * F) * g * (E * F)⁻¹) hprod
    group at h ⊢
    exact h
  simpa [A, B, C, D, E, F, sH, mul_assoc] using hrot

/-- Embedded version of the cyclically rotated C2 product calculation. -/
public theorem CFSG.appendixCEmbedding_CP0_conj_normOneUnits_C2_cyclic_product_of_add_eq_two
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {c : ZMod p} (v z : appendixCNormOneUnits p q)
    (hadd :
      (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2) :
    let sH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)
    σ sH * σ (SemidirectProduct.inr z⁻¹) * (σ sH) ^ (-2 : ℤ) *
      σ (SemidirectProduct.inr v) * σ sH *
      σ (SemidirectProduct.inr (v⁻¹ * z)) = 1 := by
  dsimp only
  let sH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd
    (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)
  have hsrc :
      sH * (SemidirectProduct.inr z⁻¹ : appendixCH p q) * sH ^ (-2 : ℤ) *
        (SemidirectProduct.inr v : appendixCH p q) * sH *
        (SemidirectProduct.inr (v⁻¹ * z) : appendixCH p q) = 1 := by
    simpa [sH] using
      appendixCP0_conj_normOneUnits_C2_cyclic_product_of_add_eq_two
        (p := p) (q := q) (c := c) v z hadd
  simpa [sH, map_mul, map_zpow] using congrArg σ hsrc


/-- Embedded Step 2 corollary used repeatedly in Appendix C Lemma C.3, Step 4:
a nontrivial `P₀` element cannot conjugate a `U` element back into `U` unless
that `U` element is trivial. -/
public theorem CFSG.appendixCEmbedding_P0_conj_U_mem_U_eq_one
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {s u : G}
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q)) (hsne : s ≠ 1)
    (hu : u ∈ Subgroup.map σ (appendixCUInH p q))
    (hmem : s * u * s⁻¹ ∈ Subgroup.map σ (appendixCUInH p q)) :
    u = 1 := by
  rcases appendixCEmbedding_P0_mul_U_mul_P0_mem_U_cases
      (p := p) (q := q) hA σ hσ hs
      ((Subgroup.map σ (appendixCP0InH p q)).inv_mem hs) hu hmem with
    htrivial | hunit
  · exact False.elim (hsne htrivial.1)
  · exact hunit.1

/-- Unit-level form of the embedded Step 2 corollary: if a nontrivial embedded
`P₀` element conjugates the image of a norm-one unit back into embedded `U`,
then the norm-one unit is trivial. -/
public theorem CFSG.appendixCEmbedding_normOneUnit_eq_one_of_P0_conj_mem_U
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {s : G}
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q)) (hsne : s ≠ 1)
    (u : appendixCNormOneUnits p q)
    (hmem : s * σ (SemidirectProduct.inr u) * s⁻¹ ∈
      Subgroup.map σ (appendixCUInH p q)) :
    u = 1 := by
  have huimg : σ (SemidirectProduct.inr u) ∈
      Subgroup.map σ (appendixCUInH p q) := by
    exact ⟨SemidirectProduct.inr u,
      (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨u, rfl⟩, rfl⟩
  have hσu : σ (SemidirectProduct.inr u) = 1 :=
    appendixCEmbedding_P0_conj_U_mem_U_eq_one
      (p := p) (q := q) hA σ hσ hs hsne huimg hmem
  have hinr : SemidirectProduct.inr u = (1 : appendixCH p q) := by
    apply hσ
    simpa using hσu
  have hright := congrArg (fun x : appendixCH p q => x.right) hinr
  simpa using hright

/-- Source C9 Step 2 package: if a nontrivial embedded `P₀` element conjugates
the image of `w^(p-1)` into embedded `U`, then condition `(A)` forces
`w = 1`. -/
public theorem CFSG.appendixCEmbedding_normOneUnits_eq_one_of_P0_conj_pow_sub_one_mem_U
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {s : G}
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q)) (hsne : s ≠ 1)
    (w : appendixCNormOneUnits p q)
    (hmem : s * σ (SemidirectProduct.inr (w ^ (p - 1))) * s⁻¹ ∈
      Subgroup.map σ (appendixCUInH p q)) :
    w = 1 := by
  have hpow : w ^ (p - 1) = 1 :=
    appendixCEmbedding_normOneUnit_eq_one_of_P0_conj_mem_U
      (p := p) (q := q) hA σ hσ hs hsne (w ^ (p - 1)) hmem
  exact appendixCNormOneUnits_eq_one_of_pow_sub_one_eq_one
    (p := p) (q := q) hA hpow

/-- Variant of the C9 Step 2 package for the source expression `w^(1-p)`,
implemented as `(w⁻¹)^(p-1)`. -/
public theorem CFSG.appendixCEmbedding_normOneUnits_eq_one_of_P0_conj_inv_pow_sub_one_mem_U
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {s : G}
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q)) (hsne : s ≠ 1)
    (w : appendixCNormOneUnits p q)
    (hmem : s * σ (SemidirectProduct.inr (w⁻¹ ^ (p - 1))) * s⁻¹ ∈
      Subgroup.map σ (appendixCUInH p q)) :
    w = 1 := by
  have hpow : w⁻¹ ^ (p - 1) = 1 :=
    appendixCEmbedding_normOneUnit_eq_one_of_P0_conj_mem_U
      (p := p) (q := q) hA σ hσ hs hsne (w⁻¹ ^ (p - 1)) hmem
  exact appendixCNormOneUnits_eq_one_of_inv_pow_sub_one_eq_one
    (p := p) (q := q) hA hpow

/-- C9 Step 2 package after using Step 3: if a nontrivial embedded `P₀`
element conjugates the image of `w^(p-1)` into the Step 3 intersection, then
condition `(A)` forces `w = 1`. -/
public theorem
    appendixCEmbedding_normOneUnits_eq_one_of_P0_conj_pow_sub_one_mem_H_inf_conjBy
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {t s : G}
    (hStep3 :
      Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) ⊓
        (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))).conjBy t =
          Subgroup.map σ (appendixCUInH p q))
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q)) (hsne : s ≠ 1)
    (w : appendixCNormOneUnits p q)
    (hmem : s * σ (SemidirectProduct.inr (w ^ (p - 1))) * s⁻¹ ∈
      Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) ⊓
        (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))).conjBy t) :
    w = 1 := by
  have hU : s * σ (SemidirectProduct.inr (w ^ (p - 1))) * s⁻¹ ∈
      Subgroup.map σ (appendixCUInH p q) := by
    simpa [hStep3] using hmem
  exact appendixCEmbedding_normOneUnits_eq_one_of_P0_conj_pow_sub_one_mem_U
    (p := p) (q := q) hA σ hσ hs hsne w hU


/-- Pure C4 algebra in the source right-conjugation convention. If the C2
product has source order `A, B, C` and the three elements `s⁻¹ t`,
`s⁻² t²`, and `s⁻³ t³` commute, then the C4 product with right-conjugated
`U`-terms is trivial. This is intentionally separate from the active
left-conjugation scaffold. -/
public theorem CFSG.appendixC_lemma_C_3_step4_C4_right_conj_of_product
    {G : Type u} [Group G] {s t A B C : G}
    (hprod : s ^ (-2 : ℤ) * A * s * B * s * C = 1)
    (h12 : (s⁻¹ * t) * (s ^ (-2 : ℤ) * t ^ 2) =
      (s ^ (-2 : ℤ) * t ^ 2) * (s⁻¹ * t))
    (h13 : (s⁻¹ * t) * (s ^ (-3 : ℤ) * t ^ 3) =
      (s ^ (-3 : ℤ) * t ^ 3) * (s⁻¹ * t))
    (h23 : (s ^ (-2 : ℤ) * t ^ 2) * (s ^ (-3 : ℤ) * t ^ 3) =
      (s ^ (-3 : ℤ) * t ^ 3) * (s ^ (-2 : ℤ) * t ^ 2)) :
    t ^ 2 * (s * (t ^ (-3 : ℤ) * A * t ^ 3) * s ^ (-2 : ℤ)) *
      t⁻¹ * (s ^ 3 * (t ^ (-2 : ℤ) * B * t ^ 2) * s ^ (-1 : ℤ)) *
      t⁻¹ * (s ^ 2 * (t⁻¹ * C * t) * s ^ (-3 : ℤ)) = 1 := by
  have hseg1 :
      t ^ 2 * s * t ^ (-3 : ℤ) = s ^ 3 * t⁻¹ * s ^ (-2 : ℤ) := by
    have h13' :
        s⁻¹ * t * s ^ (-3 : ℤ) * t ^ 3 =
          s ^ (-3 : ℤ) * t ^ 3 * s⁻¹ * t := by
      simpa [mul_assoc] using h13
    have hR :
        (s⁻¹ * t * s ^ (-3 : ℤ) * t ^ 3) *
          (s ^ (-3 : ℤ) * t ^ 3 * s⁻¹ * t)⁻¹ = 1 := by
      rw [h13']
      group
    have hE :
        t ^ 2 * s * t ^ (-3 : ℤ) *
            (s ^ 3 * t⁻¹ * s ^ (-2 : ℤ))⁻¹ = 1 := by
      calc
        t ^ 2 * s * t ^ (-3 : ℤ) *
            (s ^ 3 * t⁻¹ * s ^ (-2 : ℤ))⁻¹
            = (s ^ 3 * t⁻¹ * s) *
                ((s⁻¹ * t * s ^ (-3 : ℤ) * t ^ 3) *
                  (s ^ (-3 : ℤ) * t ^ 3 * s⁻¹ * t)⁻¹) *
                (s ^ 3 * t⁻¹ * s)⁻¹ := by
              group
        _ = 1 := by rw [hR]; group
    have h := congrArg (fun g => g * (s ^ 3 * t⁻¹ * s ^ (-2 : ℤ))) hE
    group at h
    simpa [zpow_ofNat] using h
  have hseg2 :
      t ^ 3 * s ^ (-2 : ℤ) * t⁻¹ * s ^ 3 * t ^ (-2 : ℤ) = s := by
    have h23' :
        s ^ (-2 : ℤ) * t ^ 2 * s ^ (-3 : ℤ) * t ^ 3 =
          s ^ (-3 : ℤ) * t ^ 3 * s ^ (-2 : ℤ) * t ^ 2 := by
      simpa [mul_assoc] using h23
    have hR :
        (s ^ (-2 : ℤ) * t ^ 2 * s ^ (-3 : ℤ) * t ^ 3) *
          (s ^ (-3 : ℤ) * t ^ 3 * s ^ (-2 : ℤ) * t ^ 2)⁻¹ = 1 := by
      rw [h23']
      group
    have hE :
        t ^ 3 * s ^ (-2 : ℤ) * t⁻¹ * s ^ 3 * t ^ (-2 : ℤ) *
            s⁻¹ = 1 := by
      calc
        t ^ 3 * s ^ (-2 : ℤ) * t⁻¹ * s ^ 3 * t ^ (-2 : ℤ) *
            s⁻¹
            = s ^ 3 *
                ((s ^ (-2 : ℤ) * t ^ 2 * s ^ (-3 : ℤ) * t ^ 3) *
                  (s ^ (-3 : ℤ) * t ^ 3 * s ^ (-2 : ℤ) * t ^ 2)⁻¹)⁻¹ *
                s ^ (-3 : ℤ) := by
              group
        _ = 1 := by rw [hR]; group
    have h := congrArg (fun g => g * s) hE
    group at h
    simpa [zpow_ofNat] using h
  have hseg3 : t ^ 2 * s⁻¹ * t⁻¹ * s ^ 2 * t⁻¹ = s := by
    have h12' :
        s⁻¹ * t * s ^ (-2 : ℤ) * t ^ 2 =
          s ^ (-2 : ℤ) * t ^ 2 * s⁻¹ * t := by
      simpa [mul_assoc] using h12
    have hR :
        (s⁻¹ * t * s ^ (-2 : ℤ) * t ^ 2) *
          (s ^ (-2 : ℤ) * t ^ 2 * s⁻¹ * t)⁻¹ = 1 := by
      rw [h12']
      group
    have hE : t ^ 2 * s⁻¹ * t⁻¹ * s ^ 2 * t⁻¹ * s⁻¹ = 1 := by
      calc
        t ^ 2 * s⁻¹ * t⁻¹ * s ^ 2 * t⁻¹ * s⁻¹
            = s ^ 2 *
                ((s⁻¹ * t * s ^ (-2 : ℤ) * t ^ 2) *
                  (s ^ (-2 : ℤ) * t ^ 2 * s⁻¹ * t)⁻¹)⁻¹ *
                s ^ (-2 : ℤ) := by
              group
        _ = 1 := by rw [hR]; group
    have h := congrArg (fun g => g * s) hE
    group at h
    simpa [zpow_ofNat] using h
  calc
    t ^ 2 * (s * (t ^ (-3 : ℤ) * A * t ^ 3) * s ^ (-2 : ℤ)) *
      t⁻¹ * (s ^ 3 * (t ^ (-2 : ℤ) * B * t ^ 2) * s ^ (-1 : ℤ)) *
      t⁻¹ * (s ^ 2 * (t⁻¹ * C * t) * s ^ (-3 : ℤ))
        = (t ^ 2 * s * t ^ (-3 : ℤ)) * A *
          (t ^ 3 * s ^ (-2 : ℤ) * t⁻¹ * s ^ 3 * t ^ (-2 : ℤ)) * B *
          (t ^ 2 * s⁻¹ * t⁻¹ * s ^ 2 * t⁻¹) * C * t *
          s ^ (-3 : ℤ) := by
            group
    _ = (s ^ 3 * t⁻¹ * s ^ (-2 : ℤ)) * A * s * B * s * C * t *
          s ^ (-3 : ℤ) := by
          rw [hseg1, hseg2, hseg3]
    _ = s ^ 3 * (t⁻¹ * (s ^ (-2 : ℤ) * A * s * B * s * C) * t) *
          s ^ (-3 : ℤ) := by
          group
    _ = 1 := by rw [hprod]; group

/-- Embedded C2-to-C4 bridge in the source right-conjugation convention. This
specializes the pure C4 algebra to the three-factor product obtained from
`v + z = 2` in the Appendix C semidirect product. -/
public theorem CFSG.appendixCEmbedding_CP0_conj_normOneUnits_C4_right_conj_of_add_eq_two
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {s t : G} {c : ZMod p}
    (hs : s = σ (SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)))
    (v z : appendixCNormOneUnits p q)
    (hadd :
      (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2)
    (h12 : (s⁻¹ * t) * (s ^ (-2 : ℤ) * t ^ 2) =
      (s ^ (-2 : ℤ) * t ^ 2) * (s⁻¹ * t))
    (h13 : (s⁻¹ * t) * (s ^ (-3 : ℤ) * t ^ 3) =
      (s ^ (-3 : ℤ) * t ^ 3) * (s⁻¹ * t))
    (h23 : (s ^ (-2 : ℤ) * t ^ 2) * (s ^ (-3 : ℤ) * t ^ 3) =
      (s ^ (-3 : ℤ) * t ^ 3) * (s ^ (-2 : ℤ) * t ^ 2)) :
    t ^ 2 *
        (s * (t ^ (-3 : ℤ) * σ (SemidirectProduct.inr v) * t ^ 3) *
          s ^ (-2 : ℤ)) *
      t⁻¹ *
        (s ^ 3 *
          (t ^ (-2 : ℤ) * σ (SemidirectProduct.inr (v⁻¹ * z)) * t ^ 2) *
          s ^ (-1 : ℤ)) *
      t⁻¹ *
        (s ^ 2 * (t⁻¹ * σ (SemidirectProduct.inr z⁻¹) * t) *
          s ^ (-3 : ℤ)) = 1 := by
  have hprod :
      s ^ (-2 : ℤ) * σ (SemidirectProduct.inr v) * s *
          σ (SemidirectProduct.inr (v⁻¹ * z)) * s *
          σ (SemidirectProduct.inr z⁻¹) = 1 := by
    simpa [hs, mul_assoc] using
      appendixCEmbedding_CP0_conj_normOneUnits_C2_product_of_add_eq_two
        (p := p) (q := q) σ (c := c) v z hadd
  exact appendixC_lemma_C_3_step4_C4_right_conj_of_product
    (s := s) (t := t) (A := σ (SemidirectProduct.inr v))
    (B := σ (SemidirectProduct.inr (v⁻¹ * z)))
    (C := σ (SemidirectProduct.inr z⁻¹)) hprod h12 h13 h23

/-- Powered version of the embedded C2-to-C4 bridge. This is the source C8
Frobenius step applied before the C4 product is rewritten by C5. -/
public theorem CFSG.appendixCEmbedding_CP0_conj_normOneUnits_C4_right_conj_pow_of_add_eq_two
    [Fact q.Prime]
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {s t : G} {c : ZMod p}
    (hs : s = σ (SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)))
    (v z : appendixCNormOneUnits p q)
    (hadd :
      (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2)
    (h12 : (s⁻¹ * t) * (s ^ (-2 : ℤ) * t ^ 2) =
      (s ^ (-2 : ℤ) * t ^ 2) * (s⁻¹ * t))
    (h13 : (s⁻¹ * t) * (s ^ (-3 : ℤ) * t ^ 3) =
      (s ^ (-3 : ℤ) * t ^ 3) * (s⁻¹ * t))
    (h23 : (s ^ (-2 : ℤ) * t ^ 2) * (s ^ (-3 : ℤ) * t ^ 3) =
      (s ^ (-3 : ℤ) * t ^ 3) * (s ^ (-2 : ℤ) * t ^ 2)) :
    t ^ 2 *
        (s * (t ^ (-3 : ℤ) * σ (SemidirectProduct.inr (v ^ p)) * t ^ 3) *
          s ^ (-2 : ℤ)) *
      t⁻¹ *
        (s ^ 3 *
          (t ^ (-2 : ℤ) * σ (SemidirectProduct.inr ((v⁻¹ * z) ^ p)) *
            t ^ 2) *
          s ^ (-1 : ℤ)) *
      t⁻¹ *
        (s ^ 2 * (t⁻¹ * σ (SemidirectProduct.inr (z⁻¹ ^ p)) * t) *
          s ^ (-3 : ℤ)) = 1 := by
  have hp := congrArg (fun x : appendixCField p q => x ^ p) hadd
  change
    ((((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q)) ^ p =
      (2 : appendixCField p q) ^ p at hp
  have hleft :
      ((((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) +
          (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q)) ^ p =
        (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) ^ p +
          (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) ^ p := by
    simpa [pow_one] using
      (add_pow_char_pow (R := appendixCField p q) (p := p)
        (x := (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q))
        (y := (((z : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q))
        (n := 1))
  rw [hleft] at hp
  have hadd_pow :
      (((v ^ p : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((z ^ p : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2 := by
    simpa [appendixCField_two_pow_prime_eq_two (p := p) (q := q)] using hp
  have hpow :=
    appendixCEmbedding_CP0_conj_normOneUnits_C4_right_conj_of_add_eq_two
      (p := p) (q := q) σ (s := s) (t := t) (c := c) hs
      (v ^ p) (z ^ p) hadd_pow h12 h13 h23
  simpa [mul_pow] using hpow

/-- The pure group-algebra part of Appendix C C.3 Step 4 leading to source
equation C7. Once the C4 product has been rewritten using the C5
decompositions and the `w_i` definitions, this isolates the cancellation and
cyclic rotation that gives
`t⁻¹ * s₂ * t⁻¹ = (w₁ * s₃ * w₂ * t² * s₁ * w₃)⁻¹`. -/
public theorem CFSG.appendixC_lemma_C_3_step4_C7_of_product
    {G : Type u} [Group G]
    {t u1 s1 v1 u2 s2 v2 u3 s3 v3 w1 w2 w3 : G}
    (hw1 : w1 = t * v2 * t⁻¹ * u3)
    (hw2 : w2 = v3 * (t ^ 2 * u1 * (t ^ 2)⁻¹))
    (hw3 : w3 = v1 * (t⁻¹ * u2 * (t⁻¹)⁻¹))
    (hprod :
      t ^ 2 * (u1 * s1 * v1) * t⁻¹ * (u2 * s2 * v2) *
          t⁻¹ * (u3 * s3 * v3) = 1) :
    t⁻¹ * s2 * t⁻¹ = (w1 * s3 * w2 * t ^ 2 * s1 * w3)⁻¹ := by
  subst w1
  subst w2
  subst w3
  let u1t : G := t ^ 2 * u1 * (t ^ 2)⁻¹
  let A : G := t ^ 2 * s1 * (v1 * (t⁻¹ * u2 * (t⁻¹)⁻¹))
  let B : G := t⁻¹ * s2 * t⁻¹
  let C : G := (t * v2 * t⁻¹ * u3) * s3 *
    (v3 * (t ^ 2 * u1 * (t ^ 2)⁻¹))
  have hconj : u1t * (A * B * C) * u1t⁻¹ =
      t ^ 2 * (u1 * s1 * v1) * t⁻¹ * (u2 * s2 * v2) *
        t⁻¹ * (u3 * s3 * v3) := by
    dsimp [u1t, A, B, C]
    group
  have hconj_one : u1t * (A * B * C) * u1t⁻¹ = 1 := by
    rw [hconj]
    exact hprod
  have hABC : A * B * C = 1 := by
    have h := congrArg (fun g : G => u1t⁻¹ * g * u1t) hconj_one
    dsimp [u1t, A, B, C] at h ⊢
    group at h ⊢
    exact h
  have hBCA : B * C * A = 1 := by
    have h := congrArg (fun g : G => A⁻¹ * g * A) hABC
    dsimp [A, B, C] at h ⊢
    group at h ⊢
    exact h
  rw [eq_inv_iff_mul_eq_one]
  simpa [A, B, C, mul_assoc] using hBCA

/-- Image-level form of the C7 product cleanup. This is the version used in the
condition-`(B)` ambient group after the three `w_i` have been named as abstract
norm-one units and transported through the embedding. -/
public theorem CFSG.appendixC_lemma_C_3_step4_C7_of_image_product
    {G : Type u} [Group G] {σ : appendixCH p q →* G}
    {t u1 s1 v1 u2 s2 v2 u3 s3 v3 : G}
    {w1 w2 w3 : appendixCNormOneUnits p q}
    (hw1 : σ (SemidirectProduct.inr w1) = t * v2 * t⁻¹ * u3)
    (hw2 : σ (SemidirectProduct.inr w2) = v3 * (t ^ 2 * u1 * (t ^ 2)⁻¹))
    (hw3 : σ (SemidirectProduct.inr w3) = v1 * (t⁻¹ * u2 * (t⁻¹)⁻¹))
    (hprod :
      t ^ 2 * (u1 * s1 * v1) * t⁻¹ * (u2 * s2 * v2) *
          t⁻¹ * (u3 * s3 * v3) = 1) :
    t⁻¹ * s2 * t⁻¹ =
      (σ (SemidirectProduct.inr w1) * s3 * σ (SemidirectProduct.inr w2) *
        t ^ 2 * s1 * σ (SemidirectProduct.inr w3))⁻¹ := by
  exact appendixC_lemma_C_3_step4_C7_of_product
    (t := t) (u1 := u1) (s1 := s1) (v1 := v1)
    (u2 := u2) (s2 := s2) (v2 := v2)
    (u3 := u3) (s3 := s3) (v3 := v3)
    (w1 := σ (SemidirectProduct.inr w1))
    (w2 := σ (SemidirectProduct.inr w2))
    (w3 := σ (SemidirectProduct.inr w3))
    (by simpa [mul_assoc] using hw1)
    (by simpa [mul_assoc] using hw2)
    (by simpa [mul_assoc] using hw3)
    hprod

/-- Power cancellation used in the C9 algebra when rewriting `w^(1-p)` as
`(w⁻¹)^(p-1)`. -/
private theorem CFSG.appendixC_group_inv_pow_mul_self_eq_inv_pow_sub_one_of_prime
    {G : Type u} [Group G] {p : ℕ} [Fact p.Prime] (w : G) :
    (w ^ p)⁻¹ * w = w⁻¹ ^ (p - 1) := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  cases p with
  | zero => omega
  | succ n =>
      simp only [add_tsub_cancel_right]
      rw [pow_succ]
      group

/-- Power cancellation used in the C9 algebra when rewriting `w^p * w⁻¹` as
`w^(p-1)`. -/
private theorem CFSG.appendixC_group_pow_mul_inv_eq_pow_sub_one_of_prime
    {G : Type u} [Group G] {p : ℕ} [Fact p.Prime] (w : G) :
    w ^ p * w⁻¹ = w ^ (p - 1) := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  cases p with
  | zero => omega
  | succ n =>
      simp only [add_tsub_cancel_right]
      rw [pow_succ]
      group

/-- The pure C9 algebra after the source has proved that the C7 tail is unchanged
when the `U` factors are replaced by their `p`th powers. This produces the
displayed equality in source equation C9; membership in the Step 3 intersection
and the tail collapse are handled separately. -/
public theorem CFSG.appendixC_lemma_C_3_step4_C9_eq_of_power_product
    {G : Type u} [Group G] {σ : appendixCH p q →* G}
    {t s1 s3 : G} (w1 w2 w3 : appendixCNormOneUnits p q)
    (hpowprod :
      σ (SemidirectProduct.inr w1) * s3 * σ (SemidirectProduct.inr w2) *
          t ^ 2 * s1 * σ (SemidirectProduct.inr w3) =
        σ (SemidirectProduct.inr (w1 ^ p)) * s3 *
          σ (SemidirectProduct.inr (w2 ^ p)) *
          t ^ 2 * s1 * σ (SemidirectProduct.inr (w3 ^ p))) :
    (t ^ 2)⁻¹ * (σ (SemidirectProduct.inr (w2 ^ p)))⁻¹ * s3⁻¹ *
        σ (SemidirectProduct.inr (w1⁻¹ ^ (p - 1))) * s3 *
        σ (SemidirectProduct.inr w2) * t ^ 2 =
      s1 * σ (SemidirectProduct.inr (w3 ^ (p - 1))) * s1⁻¹ := by
  let T : G := t ^ 2
  let W1 : G := σ (SemidirectProduct.inr w1)
  let W1p : G := σ (SemidirectProduct.inr (w1 ^ p))
  let W2 : G := σ (SemidirectProduct.inr w2)
  let W2p : G := σ (SemidirectProduct.inr (w2 ^ p))
  let W3 : G := σ (SemidirectProduct.inr w3)
  let W3p : G := σ (SemidirectProduct.inr (w3 ^ p))
  have hmain : T⁻¹ * W2p⁻¹ * s3⁻¹ * W1p⁻¹ * W1 * s3 * W2 * T =
      s1 * W3p * W3⁻¹ * s1⁻¹ := by
    have h' := congrArg
      (fun g : G => T⁻¹ * W2p⁻¹ * s3⁻¹ * W1p⁻¹ * g * W3⁻¹ * s1⁻¹)
      hpowprod
    dsimp [T, W1, W1p, W2, W2p, W3, W3p] at h'
    group at h'
    simpa [T, W1, W1p, W2, W2p, W3, W3p, zpow_ofNat] using h'
  have hW1diff :
      W1p⁻¹ * W1 = σ (SemidirectProduct.inr (w1⁻¹ ^ (p - 1))) := by
    dsimp [W1p, W1]
    simp [appendixC_group_inv_pow_mul_self_eq_inv_pow_sub_one_of_prime]
  have hW3diff :
      W3p * W3⁻¹ = σ (SemidirectProduct.inr (w3 ^ (p - 1))) := by
    dsimp [W3p, W3]
    simp [appendixC_group_pow_mul_inv_eq_pow_sub_one_of_prime]
  rw [← hW1diff, ← hW3diff]
  simpa [T, W1, W1p, W2, W2p, W3, W3p, mul_assoc] using hmain

/-- C9 collapse once the displayed C9 equality is available. The equality puts
the right side in the Step 3 intersection for the inverse conjugating element;
Step 3 and Step 2 force `w₃ = 1`, and the remaining group cancellation gives
the tail equality needed to force `w₁ = w₂ = 1`. -/
public theorem CFSG.appendixC_lemma_C_3_step4_C9_collapse_of_eq
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {t s1 s3 : G}
    (hStep3 :
      Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) ⊓
        (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))).conjBy ((t ^ 2)⁻¹) =
          Subgroup.map σ (appendixCUInH p q))
    (hs1 : s1 ∈ Subgroup.map σ (appendixCP0InH p q)) (hs1ne : s1 ≠ 1)
    (hs3 : s3 ∈ Subgroup.map σ (appendixCP0InH p q)) (hs3ne : s3 ≠ 1)
    (w1 w2 w3 : appendixCNormOneUnits p q)
    (hC9eq :
      (t ^ 2)⁻¹ * (σ (SemidirectProduct.inr (w2 ^ p)))⁻¹ * s3⁻¹ *
          σ (SemidirectProduct.inr (w1⁻¹ ^ (p - 1))) * s3 *
          σ (SemidirectProduct.inr w2) * t ^ 2 =
        s1 * σ (SemidirectProduct.inr (w3 ^ (p - 1))) * s1⁻¹) :
    w1 = 1 ∧ w2 = 1 ∧ w3 = 1 := by
  let Himg : Subgroup G := Subgroup.map σ (⊤ : Subgroup (appendixCH p q))
  let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let W1d : G := σ (SemidirectProduct.inr (w1⁻¹ ^ (p - 1)))
  let W2 : G := σ (SemidirectProduct.inr w2)
  let W2p : G := σ (SemidirectProduct.inr (w2 ^ p))
  let W3d : G := σ (SemidirectProduct.inr (w3 ^ (p - 1)))
  let T : G := t ^ 2
  let inner : G := W2p⁻¹ * s3⁻¹ * W1d * s3 * W2
  have hStep3T :
      Himg ⊓ Himg.conjBy T⁻¹ = Uimg := by
    simpa [Himg, Uimg, T] using hStep3
  have hC9eqT :
      T⁻¹ * W2p⁻¹ * s3⁻¹ * W1d * s3 * W2 * T =
        s1 * W3d * s1⁻¹ := by
    simpa [T, W1d, W2, W2p, W3d, mul_assoc] using hC9eq
  have hP0leH : P0img ≤ Himg := by
    intro x hx
    rcases hx with ⟨xH, _hxH, rfl⟩
    exact ⟨xH, trivial, rfl⟩
  have hUleH : Uimg ≤ Himg := by
    intro x hx
    rcases hx with ⟨xH, _hxH, rfl⟩
    exact ⟨xH, trivial, rfl⟩
  have hUimg (w : appendixCNormOneUnits p q) :
      σ (SemidirectProduct.inr w) ∈ Uimg := by
    exact ⟨SemidirectProduct.inr w,
      (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨w, rfl⟩, rfl⟩
  have hW1dU : W1d ∈ Uimg := by
    simpa [Uimg, W1d] using
      (hUimg (((w1⁻¹) ^ (p - 1) : appendixCNormOneUnits p q)))
  have hW2U : W2 ∈ Uimg := by
    simpa [Uimg, W2] using hUimg w2
  have hW2pU : W2p ∈ Uimg := by
    simpa [Uimg, W2p] using
      (hUimg ((w2 ^ p : appendixCNormOneUnits p q)))
  have hW1dH : W1d ∈ Himg := hUleH hW1dU
  have hW2H : W2 ∈ Himg := hUleH hW2U
  have hW2pH : W2p ∈ Himg := hUleH hW2pU
  have hs3H : s3 ∈ Himg := hP0leH (by simpa [P0img] using hs3)
  have hinnerH : inner ∈ Himg := by
    dsimp [inner]
    exact Himg.mul_mem
      (Himg.mul_mem
        (Himg.mul_mem
          (Himg.mul_mem (Himg.inv_mem hW2pH) (Himg.inv_mem hs3H))
          hW1dH)
        hs3H)
      hW2H
  have hmem3 : s1 * W3d * s1⁻¹ ∈ Himg ⊓ Himg.conjBy T⁻¹ := by
    constructor
    · have hs1H : s1 ∈ Himg := hP0leH (by simpa [P0img] using hs1)
      have hW3dU : W3d ∈ Uimg := by
        simpa [Uimg, W3d] using
          (hUimg ((w3 ^ (p - 1) : appendixCNormOneUnits p q)))
      have hW3dH : W3d ∈ Himg := hUleH hW3dU
      exact Himg.mul_mem (Himg.mul_mem hs1H hW3dH) (Himg.inv_mem hs1H)
    · rw [← hC9eqT]
      change T⁻¹ * W2p⁻¹ * s3⁻¹ * W1d * s3 * W2 * T ∈
        Subgroup.map (MulAut.conj T⁻¹).toMonoidHom Himg
      refine Subgroup.mem_map.mpr ⟨inner, hinnerH, ?_⟩
      simp [inner, mul_assoc]
  have hw3 : w3 = 1 :=
    appendixCEmbedding_normOneUnits_eq_one_of_P0_conj_pow_sub_one_mem_H_inf_conjBy
      (p := p) (q := q) hA σ hσ hStep3T
      (by simpa [P0img] using hs1) hs1ne w3
      (by simpa [Himg, W3d, mul_assoc] using hmem3)
  have hleft_one :
      T⁻¹ * W2p⁻¹ * s3⁻¹ * W1d * s3 * W2 * T = 1 := by
    rw [hC9eqT]
    simp [W3d, hw3]
  have htail_raw : s3⁻¹ * W1d * s3 = W2p * W2⁻¹ := by
    have h := congrArg
      (fun g : G => W2p * T * g * T⁻¹ * W2⁻¹) hleft_one
    group at h
    simpa using h
  have hW2diff : W2p * W2⁻¹ =
      σ (SemidirectProduct.inr (w2 ^ (p - 1))) := by
    dsimp [W2p, W2]
    simp [appendixC_group_pow_mul_inv_eq_pow_sub_one_of_prime]
  have htail :
      s3⁻¹ * σ (SemidirectProduct.inr (w1⁻¹ ^ (p - 1))) * s3 =
        σ (SemidirectProduct.inr (w2 ^ (p - 1))) := by
    calc
      s3⁻¹ * σ (SemidirectProduct.inr (w1⁻¹ ^ (p - 1))) * s3
          = s3⁻¹ * W1d * s3 := by simp [W1d]
      _ = W2p * W2⁻¹ := htail_raw
      _ = σ (SemidirectProduct.inr (w2 ^ (p - 1))) := hW2diff
  have hs3inv : s3⁻¹ ∈ P0img := P0img.inv_mem (by simpa [P0img] using hs3)
  have hs3inv_ne : s3⁻¹ ≠ 1 := by
    intro h
    exact hs3ne (inv_eq_one.mp h)
  have hw2pow_img : σ (SemidirectProduct.inr (w2 ^ (p - 1))) ∈ Uimg := by
    simpa [Uimg] using
      (hUimg ((w2 ^ (p - 1) : appendixCNormOneUnits p q)))
  have hmem1 :
      s3⁻¹ * σ (SemidirectProduct.inr (w1⁻¹ ^ (p - 1))) * (s3⁻¹)⁻¹ ∈
        Uimg := by
    have hmem1' :
        s3⁻¹ * σ (SemidirectProduct.inr (w1⁻¹ ^ (p - 1))) * s3 ∈
          Uimg := by
      rw [htail]
      exact hw2pow_img
    simpa using hmem1'
  have hw1 : w1 = 1 :=
    appendixCEmbedding_normOneUnits_eq_one_of_P0_conj_inv_pow_sub_one_mem_U
      (p := p) (q := q) hA σ hσ
      (by simpa [P0img] using hs3inv) hs3inv_ne w1
      (by simpa [Uimg] using hmem1)
  have hleft_one_tail :
      s3⁻¹ * σ (SemidirectProduct.inr (w1⁻¹ ^ (p - 1))) * s3 = 1 := by
    simp [hw1]
  have hσw2pow : σ (SemidirectProduct.inr (w2 ^ (p - 1))) = 1 := by
    rw [← htail]
    exact hleft_one_tail
  have hpow2 : w2 ^ (p - 1) = 1 := by
    have hinr : SemidirectProduct.inr (w2 ^ (p - 1)) =
        (1 : appendixCH p q) := by
      apply hσ
      simpa using hσw2pow
    exact SemidirectProduct.inr_injective hinr
  have hw2 : w2 = 1 :=
    appendixCNormOneUnits_eq_one_of_pow_sub_one_eq_one
      (p := p) (q := q) hA hpow2
  exact ⟨hw1, hw2, hw3⟩

/-- Pure group cleanup after the C9 collapse in Appendix C C.3 Step 4: once
`w₁ = w₂ = w₃ = 1`, the C7 equation is exactly the source equation C10. -/
public theorem CFSG.appendixC_lemma_C_3_step4_C10_of_C7
    {G : Type u} [Group G] {t s1 s2 s3 w1 w2 w3 : G}
    (hC7 :
      t⁻¹ * s2 * t⁻¹ = (w1 * s3 * w2 * t ^ 2 * s1 * w3)⁻¹)
    (hw1 : w1 = 1) (hw2 : w2 = 1) (hw3 : w3 = 1) :
    t ^ 2 * s1 * t⁻¹ * s2 * t⁻¹ * s3 = 1 := by
  subst w1
  subst w2
  subst w3
  calc
    t ^ 2 * s1 * t⁻¹ * s2 * t⁻¹ * s3 =
        t ^ 2 * s1 * (t⁻¹ * s2 * t⁻¹) * s3 := by group
    _ = t ^ 2 * s1 * ((1 * s3 * 1 * t ^ 2 * s1 * 1)⁻¹) * s3 := by
          rw [hC7]
    _ = 1 := by group


/-- `A` normalizes `B`. -/
@[expose] public def CFSG.appendixCNormalizes {G : Type*} [Group G]
    (A B : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (B : Set G)

/-- The right-conjugate `A^y = y^{-1}Ay`, matching the exponent convention in Appendix C. -/
@[expose] public def CFSG.appendixCRightConjugate {G : Type*} [Group G]
    (A : Subgroup G) (y : G) : Subgroup G :=
  A.conjBy y⁻¹

/-- Membership in the right-conjugate `A^y = y⁻¹ A y`, unfolded with the
Appendix C exponent convention. -/
public theorem CFSG.appendixCRightConjugate_mem_iff {G : Type u} [Group G]
    (A : Subgroup G) (y t : G) :
    t ∈ appendixCRightConjugate A y ↔ ∃ s : G, s ∈ A ∧ t = y⁻¹ * s * y := by
  rw [appendixCRightConjugate, Subgroup.conjBy]
  constructor
  · intro ht
    rcases ht with ⟨s, hs, hst⟩
    refine ⟨s, hs, ?_⟩
    simpa [mul_assoc] using hst.symm
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    simp [mul_assoc]

/-- A normalizing element acts on a subgroup by all integer powers. This is the
small group-theoretic closure used for the conjugated `U` factors in Appendix C
Lemma C.3, Step 4. -/
public theorem CFSG.appendixC_conj_zpow_mem_of_mem_normalizer
    {G : Type u} [Group G] {U : Subgroup G} {t u0 : G}
    (ht : t ∈ Subgroup.normalizer (U : Set G)) (hu : u0 ∈ U) (n : ℤ) :
    t ^ n * u0 * (t ^ n)⁻¹ ∈ U := by
  exact ((Subgroup.mem_normalizer_iff.mp
    ((Subgroup.normalizer (U : Set G)).zpow_mem ht n) u0).1 hu)

/-- A right-coset multiplication step for a subgroup normalized by the
intermediate representative. If `x = qy` and `x' = q'y'` modulo `Q`, then
`xx' = q'' yy'` modulo `Q` as soon as `y` normalizes `Q`. -/
public theorem CFSG.appendixC_modRight_mul_mem
    {G : Type u} [Group G] {Q : Subgroup G} {x y x' y' : G}
    (hxy : x * y⁻¹ ∈ Q) (hx'y' : x' * y'⁻¹ ∈ Q)
    (hynorm : y ∈ Subgroup.normalizer (Q : Set G)) :
    (x * x') * (y * y')⁻¹ ∈ Q := by
  have hconj : y * (x' * y'⁻¹) * y⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hynorm (x' * y'⁻¹)).1 hx'y'
  have heq :
      (x * x') * (y * y')⁻¹ =
        (x * y⁻¹) * (y * (x' * y'⁻¹) * y⁻¹) := by
    group
  rw [heq]
  exact Q.mul_mem hxy hconj

/-- The source C.3 Step 4 factors
`s^m * (u)^(t^k) * s^n`, with `s ∈ P₀` and `u ∈ U`, lie in the embedded
copy of `H = PU` whenever `t ∈ P₀^y` normalizes `U`. -/
public theorem CFSG.appendixCEmbedding_P0_zpow_conj_U_zpow_mem_image_top
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {y t s u0 : G}
    (hP1U : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCUInH p q)))
    (ht : t ∈ appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q))
    (hu : u0 ∈ Subgroup.map σ (appendixCUInH p q))
    (m k n : ℤ) :
    s ^ m * (t ^ k * u0 * (t ^ k)⁻¹) * s ^ n ∈
      Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) := by
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
  let Himg : Subgroup G := Subgroup.map σ (⊤ : Subgroup (appendixCH p q))
  have hP0leH : P0img ≤ Himg := by
    intro x hx
    rcases hx with ⟨xH, _hxH, rfl⟩
    exact ⟨xH, trivial, rfl⟩
  have hUleH : Uimg ≤ Himg := by
    intro x hx
    rcases hx with ⟨xH, _hxH, rfl⟩
    exact ⟨xH, trivial, rfl⟩
  have hsm : s ^ m ∈ Himg := Himg.zpow_mem
    (hP0leH (by simpa [P0img] using hs)) m
  have htnorm : t ∈ Subgroup.normalizer (Uimg : Set G) := by
    simpa [Uimg, P0img] using hP1U ht
  have hconjU : t ^ k * u0 * (t ^ k)⁻¹ ∈ Uimg := by
    exact appendixC_conj_zpow_mem_of_mem_normalizer (U := Uimg) htnorm
      (by simpa [Uimg] using hu) k
  have hsn : s ^ n ∈ Himg := Himg.zpow_mem
    (hP0leH (by simpa [P0img] using hs)) n
  exact Himg.mul_mem (Himg.mul_mem hsm (hUleH hconjU)) hsn

/-- Step 1 decomposition for the conjugated `U` factors appearing in Appendix C
Lemma C.3, Step 4. This packages the membership proof needed before applying
`appendixCEmbedding_exists_U_P0_U_decomposition` to the three C5 factors. -/
public theorem
    appendixCEmbedding_exists_U_P0_U_decomposition_of_P0_zpow_conj_U_zpow
    [Fact q.Prime] (hA : appendixCConditionA p q)
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {y t s u0 : G}
    (hP1U : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCUInH p q)))
    (ht : t ∈ appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q))
    (hu : u0 ∈ Subgroup.map σ (appendixCUInH p q))
    (m k n : ℤ) :
    ∃ u1 : G, u1 ∈ Subgroup.map σ (appendixCUInH p q) ∧
      ∃ s1 : G, s1 ∈ Subgroup.map σ (appendixCP0InH p q) ∧
        ∃ v1 : G, v1 ∈ Subgroup.map σ (appendixCUInH p q) ∧
          s ^ m * (t ^ k * u0 * (t ^ k)⁻¹) * s ^ n = u1 * s1 * v1 := by
  have hxH : s ^ m * (t ^ k * u0 * (t ^ k)⁻¹) * s ^ n ∈
      Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) :=
    appendixCEmbedding_P0_zpow_conj_U_zpow_mem_image_top
      (p := p) (q := q) σ hP1U ht hs hu m k n
  rcases appendixCEmbedding_exists_U_P0_U_decomposition
      (p := p) (q := q) hA σ hxH with
    ⟨u1, hu1, s1, hs1, v1, hv1, hdecomp⟩
  exact ⟨u1, hu1, s1, hs1, v1, hv1, hdecomp⟩

/-- The three source C5 decompositions in Appendix C Lemma C.3, Step 4. This
is only the Step 1 decomposition package; the following C6 nontriviality facts
still require Steps 2 and 3. -/
public theorem CFSG.appendixC_lemma_C_3_step4_C5_decompositions
    [Fact q.Prime] (hA : appendixCConditionA p q)
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {y t s aInv abInv b : G}
    (hP1U : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCUInH p q)))
    (ht : t ∈ appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q))
    (haInv : aInv ∈ Subgroup.map σ (appendixCUInH p q))
    (habInv : abInv ∈ Subgroup.map σ (appendixCUInH p q))
    (hb : b ∈ Subgroup.map σ (appendixCUInH p q))
    (k : ℤ) :
    ∃ u1 : G, u1 ∈ Subgroup.map σ (appendixCUInH p q) ∧
      ∃ s1 : G, s1 ∈ Subgroup.map σ (appendixCP0InH p q) ∧
        ∃ v1 : G, v1 ∈ Subgroup.map σ (appendixCUInH p q) ∧
          ∃ u2 : G, u2 ∈ Subgroup.map σ (appendixCUInH p q) ∧
            ∃ s2 : G, s2 ∈ Subgroup.map σ (appendixCP0InH p q) ∧
              ∃ v2 : G, v2 ∈ Subgroup.map σ (appendixCUInH p q) ∧
                ∃ u3 : G, u3 ∈ Subgroup.map σ (appendixCUInH p q) ∧
                  ∃ s3 : G, s3 ∈ Subgroup.map σ (appendixCP0InH p q) ∧
                    ∃ v3 : G, v3 ∈ Subgroup.map σ (appendixCUInH p q) ∧
                      s ^ (k - 2) * (t ^ k * aInv * (t ^ k)⁻¹) *
                          s ^ (-k + 1) = u1 * s1 * v1 ∧
                      s ^ k * (t ^ (k - 1) * abInv * (t ^ (k - 1))⁻¹) *
                          s ^ (-k + 2) = u2 * s2 * v2 ∧
                      s ^ (k - 1) * (t ^ (k - 2) * b * (t ^ (k - 2))⁻¹) *
                          s ^ (-k) = u3 * s3 * v3 := by
  rcases appendixCEmbedding_exists_U_P0_U_decomposition_of_P0_zpow_conj_U_zpow
      (p := p) (q := q) hA σ hP1U ht hs haInv (k - 2) k (-k + 1) with
    ⟨u1, hu1, s1, hs1, v1, hv1, h1⟩
  rcases appendixCEmbedding_exists_U_P0_U_decomposition_of_P0_zpow_conj_U_zpow
      (p := p) (q := q) hA σ hP1U ht hs habInv k (k - 1) (-k + 2) with
    ⟨u2, hu2, s2, hs2, v2, hv2, h2⟩
  rcases appendixCEmbedding_exists_U_P0_U_decomposition_of_P0_zpow_conj_U_zpow
      (p := p) (q := q) hA σ hP1U ht hs hb (k - 1) (k - 2) (-k) with
    ⟨u3, hu3, s3, hs3, v3, hv3, h3⟩
  exact ⟨u1, hu1, s1, hs1, v1, hv1, u2, hu2, s2, hs2, v2, hv2,
    u3, hu3, s3, hs3, v3, hv3, h1, h2, h3⟩

/-- The `U`-coordinate of a `P₀-U-P₀ = U-P₀-U` decomposition in an embedded
copy of Appendix C's semidirect product. This is the formal "modulo `P`" step
used after the source C5 decompositions. -/
public theorem CFSG.appendixCEmbedding_P0_U_P0_eq_U_P0_U_right_component
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {sL sR s0 : G} {z u v : appendixCNormOneUnits p q}
    (hsL : sL ∈ Subgroup.map σ (appendixCP0InH p q))
    (hsR : sR ∈ Subgroup.map σ (appendixCP0InH p q))
    (hs0 : s0 ∈ Subgroup.map σ (appendixCP0InH p q))
    (h : sL * σ (SemidirectProduct.inr z) * sR =
      σ (SemidirectProduct.inr u) * s0 * σ (SemidirectProduct.inr v)) :
    z = u * v := by
  rcases hsL with ⟨sLH, hsLH, rfl⟩
  rcases hsR with ⟨sRH, hsRH, rfl⟩
  rcases hs0 with ⟨s0H, hs0H, rfl⟩
  have hH : sLH * (SemidirectProduct.inr z : appendixCH p q) * sRH =
      (SemidirectProduct.inr u : appendixCH p q) * s0H *
        (SemidirectProduct.inr v : appendixCH p q) := by
    apply hσ
    simpa [map_mul] using h
  have hsLright : sLH.right = 1 := by
    rcases (appendixCP0InH_mem_iff (p := p) (q := q) sLH).1 hsLH with
      ⟨c, rfl⟩
    simp
  have hsRright : sRH.right = 1 := by
    rcases (appendixCP0InH_mem_iff (p := p) (q := q) sRH).1 hsRH with
      ⟨c, rfl⟩
    simp
  have hs0right : s0H.right = 1 := by
    rcases (appendixCP0InH_mem_iff (p := p) (q := q) s0H).1 hs0H with
      ⟨c, rfl⟩
    simp
  have hright := congrArg SemidirectProduct.right hH
  simpa [hsLright, hsRright, hs0right, mul_assoc] using hright

/-- Elements in the embedded copy of `P₀` commute. This packages the fact that
`P₀` lies in the additive field component of the Appendix C semidirect product. -/
public theorem CFSG.appendixCEmbedding_CP0InH_commute
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {a b : G}
    (ha : a ∈ Subgroup.map σ (appendixCP0InH p q))
    (hb : b ∈ Subgroup.map σ (appendixCP0InH p q)) :
    Commute a b := by
  rcases ha with ⟨aH, haH, rfl⟩
  rcases hb with ⟨bH, hbH, rfl⟩
  rcases (appendixCP0InH_mem_iff (p := p) (q := q) aH).1 haH with
    ⟨ca, rfl⟩
  rcases (appendixCP0InH_mem_iff (p := p) (q := q) bH).1 hbH with
    ⟨cb, rfl⟩
  rw [Commute]
  simp

/-- The `P₀` part of the post-C10 expression collapses because all displayed
terms lie in the embedded prime-field subgroup. -/
public theorem CFSG.appendixCEmbedding_CP0InH_C10_P0_part
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {s s1 s2 s3 : G}
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q))
    (hs1 : s1 ∈ Subgroup.map σ (appendixCP0InH p q))
    (hs2 : s2 ∈ Subgroup.map σ (appendixCP0InH p q)) :
    s ^ 2 * s1 * s⁻¹ * s2 * s⁻¹ * s3 = s1 * s2 * s3 := by
  have h1 : Commute s s1 :=
    appendixCEmbedding_CP0InH_commute (p := p) (q := q) σ hs hs1
  have h2 : Commute s s2 :=
    appendixCEmbedding_CP0InH_commute (p := p) (q := q) σ hs hs2
  have h1conj : s * s1 * s⁻¹ = s1 := by
    rw [h1.eq]
    group
  have h12 : Commute s (s1 * s2) := h1.mul_right h2
  have h12conj : s * (s1 * s2) * s⁻¹ = s1 * s2 := by
    rw [h12.eq]
    group
  rw [pow_two]
  calc
    s * s * s1 * s⁻¹ * s2 * s⁻¹ * s3
        = s * (s * s1 * s⁻¹) * s2 * s⁻¹ * s3 := by group
    _ = s * s1 * s2 * s⁻¹ * s3 := by rw [h1conj]
    _ = s * (s1 * s2) * s⁻¹ * s3 := by group
    _ = (s1 * s2) * s3 := by rw [h12conj]
    _ = s1 * s2 * s3 := by group

/-- Source C8 in prime-field coordinates: a `P₀-U-P₀ = U-P₀-U`
decomposition stays true after applying Frobenius to the three `U` terms. -/
public theorem CFSG.appendixCP0_U_CP0_eq_U_CP0_U_pow
    {cL cR c0 : ZMod p} {z u v : appendixCNormOneUnits p q}
    (h :
      (SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) cL) : appendixCP p q) :
          appendixCH p q) *
        SemidirectProduct.inr z *
        SemidirectProduct.inl (Multiplicative.ofAdd
          (algebraMap (ZMod p) (appendixCField p q) cR) : appendixCP p q) =
      (SemidirectProduct.inr u : appendixCH p q) *
        SemidirectProduct.inl (Multiplicative.ofAdd
          (algebraMap (ZMod p) (appendixCField p q) c0) : appendixCP p q) *
        SemidirectProduct.inr v) :
    (SemidirectProduct.inl (Multiplicative.ofAdd
      (algebraMap (ZMod p) (appendixCField p q) cL) : appendixCP p q) :
        appendixCH p q) *
      SemidirectProduct.inr (z ^ p) *
      SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) cR) : appendixCP p q) =
    (SemidirectProduct.inr (u ^ p) : appendixCH p q) *
      SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) c0) : appendixCP p q) *
      SemidirectProduct.inr (v ^ p) := by
  have hleft := congrArg SemidirectProduct.left h
  have hcoord := congrArg Multiplicative.toAdd hleft
  simp [appendixCAction_apply_toAdd] at hcoord
  let aL : appendixCField p q := algebraMap (ZMod p) (appendixCField p q) cL
  let aR : appendixCField p q := algebraMap (ZMod p) (appendixCField p q) cR
  let a0 : appendixCField p q := algebraMap (ZMod p) (appendixCField p q) c0
  have hpcoord := congrArg (fun x : appendixCField p q => x ^ p) hcoord
  change (aL + ((z : (appendixCField p q)ˣ) : appendixCField p q) * aR) ^ p =
    (((u : (appendixCField p q)ˣ) : appendixCField p q) * a0) ^ p at hpcoord
  have hLp : (aL + ((z : (appendixCField p q)ˣ) : appendixCField p q) * aR) ^ p =
      aL ^ p + (((z : (appendixCField p q)ˣ) : appendixCField p q) * aR) ^ p := by
    simpa [pow_one] using
      (add_pow_char_pow (R := appendixCField p q) (p := p)
        (x := aL) (y := ((z : (appendixCField p q)ˣ) : appendixCField p q) * aR)
        (n := 1))
  rw [hLp] at hpcoord
  simp [aL, aR, a0, mul_pow] at hpcoord
  have hfix (c : ZMod p) :
      ((algebraMap (ZMod p) (appendixCField p q) c) ^ p) =
        algebraMap (ZMod p) (appendixCField p q) c := by
    rw [← map_pow]
    simp [ZMod.pow_card]
  have hpcoord' :
      (algebraMap (ZMod p) (appendixCField p q)) cL +
        (((z ^ p : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) *
          (algebraMap (ZMod p) (appendixCField p q)) cR =
      (((u ^ p : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) *
          (algebraMap (ZMod p) (appendixCField p q)) c0 := by
    simpa [hfix, mul_assoc] using hpcoord
  have hright := congrArg SemidirectProduct.right h
  have hzuv : z = u * v := by
    simpa [mul_assoc] using hright
  have htoAdd_z :
      Multiplicative.toAdd (((appendixCAction p q) z ^ p)
        (Multiplicative.ofAdd (algebraMap (ZMod p) (appendixCField p q) cR))) =
      (((z ^ p : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) *
        algebraMap (ZMod p) (appendixCField p q) cR := by
    rw [← map_pow (appendixCAction p q) z p]
    rw [appendixCAction_apply_toAdd]
    simp
  have htoAdd_u :
      Multiplicative.toAdd (((appendixCAction p q) u ^ p)
        (Multiplicative.ofAdd (algebraMap (ZMod p) (appendixCField p q) c0))) =
      (((u ^ p : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) *
        algebraMap (ZMod p) (appendixCField p q) c0 := by
    rw [← map_pow (appendixCAction p q) u p]
    rw [appendixCAction_apply_toAdd]
    simp
  ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.mul_right,
      SemidirectProduct.right_inl, SemidirectProduct.right_inr,
      map_one, one_mul, mul_one]
    simpa [htoAdd_z, htoAdd_u] using hpcoord'
  · rw [hzuv]
    simp [mul_pow]

/-- Embedded form of source C8: a `P₀-U-P₀ = U-P₀-U` equality in an ambient
copy of Appendix C remains valid after applying Frobenius to the `U` terms. -/
public theorem CFSG.appendixCEmbedding_P0_U_P0_eq_U_P0_U_pow
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {sL sR s0 : G} {z u v : appendixCNormOneUnits p q}
    (hsL : sL ∈ Subgroup.map σ (appendixCP0InH p q))
    (hsR : sR ∈ Subgroup.map σ (appendixCP0InH p q))
    (hs0 : s0 ∈ Subgroup.map σ (appendixCP0InH p q))
    (h : sL * σ (SemidirectProduct.inr z) * sR =
      σ (SemidirectProduct.inr u) * s0 * σ (SemidirectProduct.inr v)) :
    sL * σ (SemidirectProduct.inr (z ^ p)) * sR =
      σ (SemidirectProduct.inr (u ^ p)) * s0 *
        σ (SemidirectProduct.inr (v ^ p)) := by
  rcases hsL with ⟨sLH, hsLH, rfl⟩
  rcases hsR with ⟨sRH, hsRH, rfl⟩
  rcases hs0 with ⟨s0H, hs0H, rfl⟩
  rcases (appendixCP0InH_mem_iff (p := p) (q := q) sLH).1 hsLH with ⟨cL, rfl⟩
  rcases (appendixCP0InH_mem_iff (p := p) (q := q) sRH).1 hsRH with ⟨cR, rfl⟩
  rcases (appendixCP0InH_mem_iff (p := p) (q := q) s0H).1 hs0H with ⟨c0, rfl⟩
  have hH :
      (SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) cL) : appendixCP p q) :
          appendixCH p q) *
        SemidirectProduct.inr z *
        SemidirectProduct.inl (Multiplicative.ofAdd
          (algebraMap (ZMod p) (appendixCField p q) cR) : appendixCP p q) =
      (SemidirectProduct.inr u : appendixCH p q) *
        SemidirectProduct.inl (Multiplicative.ofAdd
          (algebraMap (ZMod p) (appendixCField p q) c0) : appendixCP p q) *
        SemidirectProduct.inr v := by
    apply hσ
    simpa [map_mul] using h
  simpa [map_mul] using congrArg σ
    (appendixCP0_U_CP0_eq_U_CP0_U_pow (p := p) (q := q) hH)

/-- Appendix C hypothesis `(B)`. -/
@[expose] public def CFSG.appendixCConditionB : Prop :=
  ∃ G : Type*, ∃ _ : Group G, ∃ σ : appendixCH p q →* G,
    Function.Injective σ ∧
    ∃ Q : Subgroup G, Finite Q ∧ IsMulCommutative Q ∧
      Nat.Coprime p (Nat.card Q) ∧
      ∃ y : G, y ∈ Q ∧
        appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q ∧
        appendixCNormalizes
          (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
          (Subgroup.map σ (appendixCUInH p q))

/-- Constructor for Appendix C hypothesis `(B)` from explicit embedding and
normalizer data. -/
public theorem CFSG.appendixCConditionB_of_embeddingData
    {G : Type u} [Group G]
    (σ : appendixCH p q →* G) (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hcop : Nat.Coprime p (Nat.card Q))
    (y : G) (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hP0yU :
      appendixCNormalizes
        (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
        (Subgroup.map σ (appendixCUInH p q))) :
    appendixCConditionB.{u} p q := by
  exact ⟨G, inferInstance, σ, hσ, Q, inferInstance, inferInstance,
    hcop, y, hy, hP0Q, hP0yU⟩

/-- First inclusion in Appendix C Lemma C.3, Step 3. If `t₁` lies in the
right-conjugate `P₁ = P₀^y` and `P₁` normalizes `U`, then the embedded `U`
lies in `PU ∩ (PU)^{t₁}`. -/
public theorem CFSG.appendixCEmbedding_U_le_H_inf_conjBy_of_mem_rightConjugate
    {G : Type u} [Group G] (σ : appendixCH p q →* G) {y t1 : G}
    (ht1 : t1 ∈ appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
    (hP1U : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCUInH p q))) :
    Subgroup.map σ (appendixCUInH p q) ≤
      Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) ⊓
        (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))).conjBy t1 := by
  intro u hu
  constructor
  · rcases hu with ⟨uH, _huH, rfl⟩
    exact ⟨uH, trivial, rfl⟩
  · have ht1norm :
        t1 ∈ Subgroup.normalizer (Subgroup.map σ (appendixCUInH p q) : Set G) :=
      hP1U ht1
    have ht1invnorm :
        t1⁻¹ ∈ Subgroup.normalizer (Subgroup.map σ (appendixCUInH p q) : Set G) :=
      (Subgroup.normalizer (Subgroup.map σ (appendixCUInH p q) : Set G)).inv_mem
        ht1norm
    have hpreU : t1⁻¹ * u * t1 ∈ Subgroup.map σ (appendixCUInH p q) := by
      simpa using
        ((Subgroup.mem_normalizer_iff.mp ht1invnorm u).1 hu)
    have hpreH :
        t1⁻¹ * u * t1 ∈ Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) := by
      rcases hpreU with ⟨uH, _huH, huH_eq⟩
      exact ⟨uH, trivial, huH_eq⟩
    change u ∈ Subgroup.map (MulAut.conj t1).toMonoidHom
      (Subgroup.map σ (⊤ : Subgroup (appendixCH p q)))
    exact Subgroup.mem_map.mpr ⟨t1⁻¹ * u * t1, hpreH, by
      simp [MulAut.conj_apply, mul_assoc]⟩

/-- In Appendix C Lemma C.3, Step 3, once an element `x ∈ X` is written
as `x = s * u` with `s ∈ P`, `u ∈ U`, and `U ≤ X`, the `P`-part `s` lies
in `P ∩ X`. This isolates the source line `s' = x (u')⁻¹ ∈ P ∩ X`. -/
public theorem CFSG.appendixCEmbedding_P_part_mem_inf_of_decomposition
    {G : Type u} [Group G] (σ : appendixCH p q →* G) {X : Subgroup G}
    {x s u : G}
    (hUleX : Subgroup.map σ (appendixCUInH p q) ≤ X)
    (hxX : x ∈ X)
    (hsP : s ∈ Subgroup.map σ (appendixCPInH p q))
    (huU : u ∈ Subgroup.map σ (appendixCUInH p q))
    (hx : x = s * u) :
    s ∈ Subgroup.map σ (appendixCPInH p q) ⊓ X := by
  constructor
  · exact hsP
  · have huX : u ∈ X := hUleX huU
    have hxu : x * u⁻¹ ∈ X := X.mul_mem hxX (X.inv_mem huX)
    have hs_eq : s = x * u⁻¹ := by
      rw [hx]
      group
    simpa [hs_eq] using hxu

/-- Appendix C Lemma C.3, Step 3: if `X ≤ PU` and `U ≤ X`, then every
element of `X` lies in the subgroup generated by `P ∩ X` and `U`. -/
public theorem CFSG.appendixCEmbedding_le_P_inf_sup_U_of_le_H
    {G : Type u} [Group G] (σ : appendixCH p q →* G) {X : Subgroup G}
    (hXleH : X ≤ Subgroup.map σ (⊤ : Subgroup (appendixCH p q)))
    (hUleX : Subgroup.map σ (appendixCUInH p q) ≤ X) :
    X ≤ (Subgroup.map σ (appendixCPInH p q) ⊓ X) ⊔
      Subgroup.map σ (appendixCUInH p q) := by
  intro x hxX
  rcases appendixCEmbedding_exists_P_U_decomposition (p := p) (q := q) σ
      (hXleH hxX) with
    ⟨s, hsP, u, huU, hx⟩
  have hsPX : s ∈ Subgroup.map σ (appendixCPInH p q) ⊓ X :=
    appendixCEmbedding_P_part_mem_inf_of_decomposition
      (p := p) (q := q) σ hUleX hxX hsP huU hx
  rw [hx]
  exact ((Subgroup.map σ (appendixCPInH p q) ⊓ X) ⊔
      Subgroup.map σ (appendixCUInH p q)).mul_mem
    (Subgroup.mem_sup_left hsPX)
    (Subgroup.mem_sup_right huU)

/-- Appendix C Lemma C.3, Step 3, packaged as the source equality
`X = (P ∩ X)U`, in subgroup-generated form. -/
public theorem CFSG.appendixCEmbedding_eq_P_inf_sup_U_of_le_H
    {G : Type u} [Group G] (σ : appendixCH p q →* G) {X : Subgroup G}
    (hXleH : X ≤ Subgroup.map σ (⊤ : Subgroup (appendixCH p q)))
    (hUleX : Subgroup.map σ (appendixCUInH p q) ≤ X) :
    X = (Subgroup.map σ (appendixCPInH p q) ⊓ X) ⊔
      Subgroup.map σ (appendixCUInH p q) := by
  apply le_antisymm
  · exact appendixCEmbedding_le_P_inf_sup_U_of_le_H
      (p := p) (q := q) σ hXleH hUleX
  · exact sup_le (by intro x hx; exact hx.2) hUleX

/-- Irreducibility core for Appendix C Remark (VIII): under condition `(A)`,
an additive subgroup of `F_{p^q}` that is stable under multiplication by all
norm-one units is either trivial or all of `P`. -/
public theorem CFSG.appendixCP_subgroup_eq_bot_or_top_of_normOneUnits_smul
    [Fact q.Prime]
    (hA : appendixCConditionA p q)
    {K : Subgroup (appendixCP p q)}
    (hU : ∀ u : appendixCNormOneUnits p q, ∀ z : appendixCField p q,
      Multiplicative.ofAdd z ∈ K →
        Multiplicative.ofAdd
          (((u : (appendixCField p q)ˣ) : appendixCField p q) * z) ∈ K) :
    K = ⊥ ∨ K = ⊤ := by
  by_cases hKbot : K = ⊥
  · exact Or.inl hKbot
  · right
    apply eq_top_iff.mpr
    intro y _hy
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hKbot with ⟨x, hxne⟩
    have hx0 : Multiplicative.toAdd (x : appendixCP p q) ≠ 0 := by
      intro hx0
      apply hxne
      ext
      simpa using hx0
    by_cases hy0 : Multiplicative.toAdd y = 0
    · have hyone : y = 1 := by
        ext
        simpa using hy0
      simp [hyone]
    · let ratio : (appendixCField p q)ˣ :=
        Units.mk0 (Multiplicative.toAdd y / Multiplicative.toAdd (x : appendixCP p q))
          (div_ne_zero hy0 hx0)
      rcases appendixCFieldUnit_eq_primeField_mul_normOneUnit (p := p) (q := q)
          hA ratio with
        ⟨c, u, hratio⟩
      have hxK : (x : appendixCP p q) ∈ K := x.property
      have huxK : Multiplicative.ofAdd
          (((u : (appendixCField p q)ˣ) : appendixCField p q) *
            Multiplicative.toAdd (x : appendixCP p q)) ∈ K :=
        hU u (Multiplicative.toAdd (x : appendixCP p q)) hxK
      let S : Submodule (ZMod p) (appendixCField p q) :=
        AddSubgroup.toZModSubmodule (n := p) (Subgroup.toAddSubgroup' K)
      have huxS :
          ((u : (appendixCField p q)ˣ) : appendixCField p q) *
            Multiplicative.toAdd (x : appendixCP p q) ∈ S := by
        simpa [S] using (Subgroup.mem_toAddSubgroup' K _).2 huxK
      have hscalarS :
          (c : ZMod p) •
            (((u : (appendixCField p q)ˣ) : appendixCField p q) *
              Multiplicative.toAdd (x : appendixCP p q)) ∈ S :=
        S.smul_mem (c : ZMod p) huxS
      have hyfield : Multiplicative.toAdd y =
          algebraMap (ZMod p) (appendixCField p q) (c : ZMod p) *
            (((u : (appendixCField p q)ˣ) : appendixCField p q) *
              Multiplicative.toAdd (x : appendixCP p q)) := by
        have hratio' :
            Multiplicative.toAdd y / Multiplicative.toAdd (x : appendixCP p q) =
              algebraMap (ZMod p) (appendixCField p q) (c : ZMod p) *
                ((u : (appendixCField p q)ˣ) : appendixCField p q) := by
          simpa [ratio] using hratio
        calc
          Multiplicative.toAdd y =
              (Multiplicative.toAdd y / Multiplicative.toAdd (x : appendixCP p q)) *
                Multiplicative.toAdd (x : appendixCP p q) := by
                field_simp [hx0]
          _ = (algebraMap (ZMod p) (appendixCField p q) (c : ZMod p) *
                ((u : (appendixCField p q)ˣ) : appendixCField p q)) *
                Multiplicative.toAdd (x : appendixCP p q) := by
                rw [hratio']
          _ = algebraMap (ZMod p) (appendixCField p q) (c : ZMod p) *
                (((u : (appendixCField p q)ˣ) : appendixCField p q) *
                  Multiplicative.toAdd (x : appendixCP p q)) := by
                ring
      have hyS : Multiplicative.toAdd y ∈ S := by
        simpa [hyfield, Algebra.smul_def] using hscalarS
      have hyAdd : Multiplicative.toAdd y ∈ Subgroup.toAddSubgroup' K := by
        simpa [S] using hyS
      simpa using (Subgroup.mem_toAddSubgroup' K (Multiplicative.toAdd y)).1 hyAdd

/-- Semidirect-product form of the Appendix C irreducibility fact: if
`K ≤ P` is normalized by `U`, then `K` is either trivial or all of `P`. -/
public theorem CFSG.appendixCPInH_subgroup_eq_bot_or_top_of_U_normalizes
    [Fact q.Prime]
    (hA : appendixCConditionA p q)
    {K : Subgroup (appendixCH p q)}
    (hKleP : K ≤ appendixCPInH p q)
    (hUnorm : appendixCUInH p q ≤ Subgroup.normalizer (K : Set (appendixCH p q))) :
    K = ⊥ ∨ K = appendixCPInH p q := by
  let KP : Subgroup (appendixCP p q) := Subgroup.comap SemidirectProduct.inl K
  have hUaction : ∀ u : appendixCNormOneUnits p q, ∀ z : appendixCField p q,
      Multiplicative.ofAdd z ∈ KP →
        Multiplicative.ofAdd
          (((u : (appendixCField p q)ˣ) : appendixCField p q) * z) ∈ KP := by
    intro u z hz
    let uH : appendixCH p q := SemidirectProduct.inr u
    let zH : appendixCH p q := SemidirectProduct.inl (Multiplicative.ofAdd z)
    have hzK : zH ∈ K := by
      simpa [KP, zH] using hz
    have huHmem : uH ∈ appendixCUInH p q := by
      exact (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨u, rfl⟩
    have hunorm : uH ∈ Subgroup.normalizer (K : Set (appendixCH p q)) :=
      hUnorm huHmem
    have hconj : uH * zH * uH⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hunorm zH).1 hzK
    have hact : (appendixCAction p q u) (Multiplicative.ofAdd z) =
        Multiplicative.ofAdd
          (((u : (appendixCField p q)ˣ) : appendixCField p q) * z) := by
      ext
      exact appendixCAction_apply_toAdd (p := p) (q := q) u (Multiplicative.ofAdd z)
    have htarget : (SemidirectProduct.inl
          (Multiplicative.ofAdd
            (((u : (appendixCField p q)ˣ) : appendixCField p q) * z)) :
          appendixCH p q) ∈ K := by
      have hconjeq : (SemidirectProduct.inl
            (Multiplicative.ofAdd
              (((u : (appendixCField p q)ˣ) : appendixCField p q) * z)) :
            appendixCH p q) = uH * zH * uH⁻¹ := by
        change (SemidirectProduct.inl
            (Multiplicative.ofAdd
              (((u : (appendixCField p q)ˣ) : appendixCField p q) * z)) :
            appendixCH p q) =
          (SemidirectProduct.inr u : appendixCH p q) *
            (SemidirectProduct.inl (Multiplicative.ofAdd z) : appendixCH p q) *
            (SemidirectProduct.inr u : appendixCH p q)⁻¹
        simpa [hact] using
          (SemidirectProduct.inl_aut (φ := appendixCAction p q) u (Multiplicative.ofAdd z))
      simpa [hconjeq] using hconj
    exact htarget
  rcases appendixCP_subgroup_eq_bot_or_top_of_normOneUnits_smul
      (p := p) (q := q) hA (K := KP) hUaction with hKPbot | hKPtop
  · left
    apply le_antisymm
    · intro x hx
      rcases (appendixCPInH_mem_iff (p := p) (q := q) x).1 (hKleP hx) with
        ⟨z, rfl⟩
      have hzKP : z ∈ KP := hx
      have hzbot : z ∈ (⊥ : Subgroup (appendixCP p q)) := by
        simpa [hKPbot] using hzKP
      have hz1 : z = 1 := by
        simpa using hzbot
      simp [hz1]
    · exact bot_le
  · right
    apply le_antisymm hKleP
    intro x hxP
    rcases (appendixCPInH_mem_iff (p := p) (q := q) x).1 hxP with ⟨z, rfl⟩
    have hzKP : z ∈ KP := by
      simp [hKPtop]
    simpa [KP] using hzKP

/-- Embedded irreducibility form used in Appendix C Lemma C.3, Step 3:
if an ambient subgroup `X` contains the embedded `U`, then
`image(P) ∩ X` is either trivial or all of `image(P)`. -/
public theorem CFSG.appendixCEmbedding_CPInH_inf_X_eq_bot_or_eq_CPInH_of_U_le_X
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {X : Subgroup G}
    (hUleX : Subgroup.map σ (appendixCUInH p q) ≤ X) :
    Subgroup.map σ (appendixCPInH p q) ⊓ X = ⊥ ∨
      Subgroup.map σ (appendixCPInH p q) ⊓ X =
        Subgroup.map σ (appendixCPInH p q) := by
  let K : Subgroup (appendixCH p q) :=
    Subgroup.comap σ (Subgroup.map σ (appendixCPInH p q) ⊓ X)
  have hKleP : K ≤ appendixCPInH p q := by
    intro h hh
    have hσhP : σ h ∈ Subgroup.map σ (appendixCPInH p q) := hh.1
    rcases hσhP with ⟨pH, hpH, hσp⟩
    have hp_eq : pH = h := hσ hσp
    simpa [hp_eq] using hpH
  have hUnorm : appendixCUInH p q ≤
      Subgroup.normalizer (K : Set (appendixCH p q)) := by
    have hforward : ∀ {g k : appendixCH p q}, g ∈ appendixCUInH p q →
        k ∈ K → g * k * g⁻¹ ∈ K := by
      intro g k hg hk
      constructor
      · have hkP : k ∈ appendixCPInH p q := hKleP hk
        have hconjP : g * k * g⁻¹ ∈ appendixCPInH p q :=
          ((inferInstance : (appendixCPInH p q).Normal).conj_mem k hkP g)
        exact ⟨g * k * g⁻¹, hconjP, rfl⟩
      · have hσgX : σ g ∈ X := hUleX ⟨g, hg, rfl⟩
        have hσkX : σ k ∈ X := hk.2
        simpa [map_mul] using X.mul_mem (X.mul_mem hσgX hσkX) (X.inv_mem hσgX)
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hforward hu hk
    · intro hconj
      have huinv : u⁻¹ ∈ appendixCUInH p q := (appendixCUInH p q).inv_mem hu
      have hback : u⁻¹ * (u * k * u⁻¹) * (u⁻¹)⁻¹ ∈ K :=
        hforward huinv hconj
      simpa [mul_assoc] using hback
  rcases appendixCPInH_subgroup_eq_bot_or_top_of_U_normalizes
      (p := p) (q := q) hA (K := K) hKleP hUnorm with hKbot | hKtop
  · left
    apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨h, hhP, rfl⟩
      have hhK : h ∈ K := by
        constructor
        · exact ⟨h, hhP, rfl⟩
        · exact hx.2
      have hhbot : h ∈ (⊥ : Subgroup (appendixCH p q)) := by
        simpa [hKbot] using hhK
      have hh1 : h = 1 := by
        simpa using hhbot
      simp [hh1]
    · exact bot_le
  · right
    apply le_antisymm inf_le_left
    intro x hxP
    constructor
    · exact hxP
    · rcases hxP with ⟨h, hhP, rfl⟩
      have hhK : h ∈ K := by
        simpa [hKtop] using hhP
      exact hhK.2

/-- Appendix C Lemma C.3, Step 3 irreducibility consequence: if
`X ≤ image(PU)`, `image(U) ≤ X`, and `X` is not just `image(U)`, then
`X = image(PU)`. -/
public theorem CFSG.appendixCEmbedding_eq_image_top_of_ne_U_of_le_H
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {X : Subgroup G}
    (hXleH : X ≤ Subgroup.map σ (⊤ : Subgroup (appendixCH p q)))
    (hUleX : Subgroup.map σ (appendixCUInH p q) ≤ X)
    (hXneU : X ≠ Subgroup.map σ (appendixCUInH p q)) :
    X = Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) := by
  have hXeq : X = (Subgroup.map σ (appendixCPInH p q) ⊓ X) ⊔
      Subgroup.map σ (appendixCUInH p q) :=
    appendixCEmbedding_eq_P_inf_sup_U_of_le_H (p := p) (q := q) σ hXleH hUleX
  rcases appendixCEmbedding_CPInH_inf_X_eq_bot_or_eq_CPInH_of_U_le_X
      (p := p) (q := q) hA σ hσ hUleX with hPbot | hPtop
  · exfalso
    apply hXneU
    calc
      X = (Subgroup.map σ (appendixCPInH p q) ⊓ X) ⊔
          Subgroup.map σ (appendixCUInH p q) := hXeq
      _ = (⊥ : Subgroup G) ⊔ Subgroup.map σ (appendixCUInH p q) := by
          rw [hPbot]
      _ = Subgroup.map σ (appendixCUInH p q) := by
          simp
  · calc
      X = (Subgroup.map σ (appendixCPInH p q) ⊓ X) ⊔
          Subgroup.map σ (appendixCUInH p q) := hXeq
      _ = Subgroup.map σ (appendixCPInH p q) ⊔
          Subgroup.map σ (appendixCUInH p q) := by
          rw [hPtop]
      _ = Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) :=
          appendixCEmbedding_CPInH_sup_CUInH_eq_image_top (p := p) (q := q) σ

/-- If a finite subgroup `H` satisfies `H ∩ H.conjBy t = H`, then `t`
normalizes `H`. This is the finite-cardinality step used in Appendix C C.3
after proving `(PU) ∩ (PU)^{t₁} = PU`. -/
public theorem CFSG.appendixC_mem_normalizer_of_inf_conjBy_eq_left
    {G : Type u} [Group G] (H : Subgroup G) [Finite H] {t : G}
    (h : H ⊓ H.conjBy t = H) :
    t ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H ≤ H.conjBy t := by
    intro x hx
    have hxinf : x ∈ H ⊓ H.conjBy t := by
      simpa [h] using hx
    exact hxinf.2
  have htinv : t⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro n hn
    have hn_conj : n ∈ H.conjBy t := hle hn
    change n ∈ Subgroup.map (MulAut.conj t).toMonoidHom H at hn_conj
    rcases hn_conj with ⟨h0, hh0, hnh0⟩
    have hpre : t⁻¹ * n * (t⁻¹)⁻¹ = h0 := by
      rw [← hnh0]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hpre]
    exact hh0
  simpa using (Subgroup.normalizer (H : Set G)).inv_mem htinv

/-- Appendix C C.3 specialization of
`appendixC_mem_normalizer_of_inf_conjBy_eq_left`: if the embedded
`PU ∩ (PU)^t` equals embedded `PU`, then `t` normalizes embedded `PU`. -/
public theorem CFSG.appendixCEmbedding_image_top_mem_normalizer_of_inf_conjBy_eq_image_top
    {G : Type u} [Group G] (σ : appendixCH p q →* G) {t : G}
    (h : Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) ⊓
        (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))).conjBy t =
          Subgroup.map σ (⊤ : Subgroup (appendixCH p q))) :
    t ∈ Subgroup.normalizer
      (Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) : Set G) := by
  classical
  have : Finite (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))) := by
    have hfiniteSet :
        ((Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) : Subgroup G) :
          Set G).Finite := by
      change (σ '' ((⊤ : Subgroup (appendixCH p q)) : Set (appendixCH p q))).Finite
      exact Set.Finite.image σ (Set.toFinite _)
    exact hfiniteSet.to_subtype
  exact appendixC_mem_normalizer_of_inf_conjBy_eq_left
    (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))) h

/-- A nontrivial member of `E` gives a nontrivial norm-one unit. -/
public theorem CFSG.appendixCE_exists_nontrivial_normOneUnit
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
    ∃ u : appendixCNormOneUnits p q, u ≠ 1 := by
  let aU : appendixCNormOneUnits p q :=
    ⟨Units.mk0 a (appendixCE_ne_zero (p := p) (q := q) ha),
      appendixCE_unit_mem_normOneUnits (p := p) (q := q) ha⟩
  refine ⟨aU, ?_⟩
  intro h
  apply ha1
  have hfield := congrArg (fun u : appendixCNormOneUnits p q =>
    ((u : (appendixCField p q)ˣ) : appendixCField p q)) h
  simpa [aU] using hfield

/-- In `PU`, the commutator subgroup is contained in `P`. -/
public theorem CFSG.appendixCH_commutator_le_CPInH :
    commutator (appendixCH p q) ≤ appendixCPInH p q := by
  rw [commutator]
  rw [Subgroup.commutator_le]
  intro a _ha b _hb
  rw [appendixCPInH_mem_iff]
  refine ⟨SemidirectProduct.left ⁅a, b⁆, ?_⟩
  ext <;> simp [commutatorElement_def]

/-- A nontrivial norm-one unit makes the commutator subgroup of `PU`
nontrivial. -/
public theorem CFSG.appendixCH_commutator_ne_bot_of_nontrivial_normOneUnit
    {u : appendixCNormOneUnits p q} (hu : u ≠ 1) :
    commutator (appendixCH p q) ≠ ⊥ := by
  intro hbot
  let c : appendixCH p q := ⁅(SemidirectProduct.inr u : appendixCH p q),
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : appendixCField p q)) :
        appendixCH p q)⁆
  have hc_mem : c ∈ commutator (appendixCH p q) := by
    change c ∈ ⁅(⊤ : Subgroup (appendixCH p q)),
      (⊤ : Subgroup (appendixCH p q))⁆
    exact Subgroup.commutator_mem_commutator (by simp) (by simp)
  have hc_bot : c ∈ (⊥ : Subgroup (appendixCH p q)) := by
    simpa [hbot] using hc_mem
  have hc_one : c = 1 := by
    simpa using hc_bot
  have hc_ne : c ≠ 1 := by
    dsimp [c]
    intro hcomm
    have hleft := congrArg SemidirectProduct.left hcomm
    have hzero :
        ((u : (appendixCField p q)ˣ) : appendixCField p q) + -1 = 0 := by
      simpa [commutatorElement_def, appendixCAction_apply_toAdd] using
        congrArg Multiplicative.toAdd hleft
    have hfield : ((u : (appendixCField p q)ˣ) : appendixCField p q) = 1 := by
      linear_combination hzero
    apply hu
    apply Subtype.ext
    apply Units.ext
    exact hfield
  exact hc_ne hc_one

/-- Under condition `(A)`, if the norm-one subgroup is nontrivial, then
`P = [PU, PU]`. This is the characteristicity route for the source sentence
"Since `P` is characteristic in `PU`". -/
public theorem CFSG.appendixCPInH_eq_commutator_of_nontrivial_normOneUnit
    [Fact q.Prime]
    (hA : appendixCConditionA p q)
    {u : appendixCNormOneUnits p q} (hu : u ≠ 1) :
    appendixCPInH p q = commutator (appendixCH p q) := by
  have hUnorm : appendixCUInH p q ≤
      Subgroup.normalizer (commutator (appendixCH p q) : Set (appendixCH p q)) := by
    intro g _hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact (inferInstance : (commutator (appendixCH p q)).Normal).conj_mem k hk g
    · intro hk
      have hback : g⁻¹ * (g * k * g⁻¹) * (g⁻¹)⁻¹ ∈
          commutator (appendixCH p q) :=
        (inferInstance : (commutator (appendixCH p q)).Normal).conj_mem
          (g * k * g⁻¹) hk g⁻¹
      simpa [mul_assoc] using hback
  rcases appendixCPInH_subgroup_eq_bot_or_top_of_U_normalizes
      (p := p) (q := q) hA (K := commutator (appendixCH p q))
      (appendixCH_commutator_le_CPInH (p := p) (q := q)) hUnorm with
    hbot | htop
  · exfalso
    exact appendixCH_commutator_ne_bot_of_nontrivial_normOneUnit (p := p) (q := q)
      hu hbot
  · exact htop.symm


/-- Any element normalizing a subgroup also normalizes that subgroup's
commutator subgroup. -/
public theorem CFSG.appendixC_normalizer_le_normalizer_commutator
    {G : Type u} [Group G] (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  intro t ht
  have hmapH : Subgroup.map (MulAut.conj t).toMonoidHom H = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp ht y).1 hy
    · intro hx
      refine ⟨t⁻¹ * x * t, ?_, ?_⟩
      · have htinv : t⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
          (Subgroup.normalizer (H : Set G)).inv_mem ht
        simpa using ((Subgroup.mem_normalizer_iff.mp htinv x).1 hx)
      · simp [MulAut.conj_apply, mul_assoc]
  have hmapComm : Subgroup.map (MulAut.conj t).toMonoidHom ⁅H, H⁆ = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, hmapH]
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have hmem : (MulAut.conj t).toMonoidHom k ∈ ⁅H, H⁆ := by
      rw [← hmapComm]
      exact ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply] using hmem
  · intro hk
    have htinv : t⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem ht
    have hmapHinv : Subgroup.map (MulAut.conj t⁻¹).toMonoidHom H = H := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp htinv y).1 hy
      · intro hx
        refine ⟨t * x * t⁻¹, ?_, ?_⟩
        · simpa using ((Subgroup.mem_normalizer_iff.mp ht x).1 hx)
        · simp [mul_assoc]
    have hmapComminv :
        Subgroup.map (MulAut.conj t⁻¹).toMonoidHom ⁅H, H⁆ = ⁅H, H⁆ := by
      rw [Subgroup.map_commutator, hmapHinv]
    have hpre : (MulAut.conj t⁻¹).toMonoidHom (t * k * t⁻¹) ∈ ⁅H, H⁆ := by
      rw [← hmapComminv]
      exact ⟨t * k * t⁻¹, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hpre

/-- Embedded form of `P = [PU, PU]`, using a nontrivial member of `E`. -/
public theorem CFSG.appendixCEmbedding_CPInH_eq_commutator_of_mem_appendixCE_ne_one
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
    Subgroup.map σ (appendixCPInH p q) =
      ⁅Subgroup.map σ (⊤ : Subgroup (appendixCH p q)),
        Subgroup.map σ (⊤ : Subgroup (appendixCH p q))⁆ := by
  rcases appendixCE_exists_nontrivial_normOneUnit (p := p) (q := q) ha ha1 with
    ⟨u, hu⟩
  rw [appendixCPInH_eq_commutator_of_nontrivial_normOneUnit
    (p := p) (q := q) hA hu]
  rw [commutator]
  exact Subgroup.map_commutator (⊤ : Subgroup (appendixCH p q))
    (⊤ : Subgroup (appendixCH p q)) σ

/-- If a nontrivial element of `E` is available, then every normalizer of the
embedded `PU` normalizes the embedded `P`. -/
public theorem CFSG.appendixCEmbedding_image_top_normalizer_le_CPInH_normalizer_of_mem_appendixCE_ne_one
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
    Subgroup.normalizer
      (Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) : Set G) ≤
        Subgroup.normalizer (Subgroup.map σ (appendixCPInH p q) : Set G) := by
  intro t ht
  have hComm :
      Subgroup.map σ (appendixCPInH p q) =
        ⁅Subgroup.map σ (⊤ : Subgroup (appendixCH p q)),
          Subgroup.map σ (⊤ : Subgroup (appendixCH p q))⁆ :=
    appendixCEmbedding_CPInH_eq_commutator_of_mem_appendixCE_ne_one
      (p := p) (q := q) hA σ ha ha1
  have htcomm :
      t ∈ Subgroup.normalizer
        ((⁅Subgroup.map σ (⊤ : Subgroup (appendixCH p q)),
            Subgroup.map σ (⊤ : Subgroup (appendixCH p q))⁆ : Subgroup G) : Set G) :=
    appendixC_normalizer_le_normalizer_commutator
      (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))) ht
  simpa [hComm] using htcomm

/-- Appendix C C.3 Step 3, through the characteristicity sentence: for
`X = PU ∩ (PU)^t`, if embedded `U ≤ X` and `X ≠ U`, then `t` normalizes the
embedded `P`. -/
public theorem CFSG.appendixCEmbedding_CPInH_mem_normalizer_of_H_inf_conjBy_ne_U
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {t : G}
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1)
    (hUleX : Subgroup.map σ (appendixCUInH p q) ≤
      Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) ⊓
        (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))).conjBy t)
    (hXneU : Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) ⊓
        (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))).conjBy t ≠
      Subgroup.map σ (appendixCUInH p q)) :
    t ∈ Subgroup.normalizer (Subgroup.map σ (appendixCPInH p q) : Set G) := by
  let Himg : Subgroup G := Subgroup.map σ (⊤ : Subgroup (appendixCH p q))
  let X : Subgroup G := Himg ⊓ Himg.conjBy t
  have hXeqH : X = Himg := by
    exact appendixCEmbedding_eq_image_top_of_ne_U_of_le_H
      (p := p) (q := q) hA σ hσ (X := X) inf_le_left hUleX hXneU
  have htH : t ∈ Subgroup.normalizer (Himg : Set G) := by
    exact appendixCEmbedding_image_top_mem_normalizer_of_inf_conjBy_eq_image_top
      (p := p) (q := q) σ (t := t) hXeqH
  exact appendixCEmbedding_image_top_normalizer_le_CPInH_normalizer_of_mem_appendixCE_ne_one
    (p := p) (q := q) hA σ ha ha1 htH

/-- Source Step 3 subgroup calculation: if `P₀ ≤ P`, `P₀` normalizes `Q`,
and `P ∩ Q = 1`, then `P ∩ QP₀ = P₀` (with `QP₀` represented by the join
`Q ⊔ P₀`). -/
public theorem CFSG.appendixC_inf_sup_eq_of_inf_eq_bot_of_le_of_normalizes
    {G : Type u} [Group G] {P Q P0 : Subgroup G}
    (hP0P : P0 ≤ P)
    (hP0Q : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hPQ : P ⊓ Q = ⊥) :
    P ⊓ (Q ⊔ P0) = P0 := by
  apply le_antisymm
  · intro x hx
    have hxProd : x ∈ (Q : Set G) * (P0 : Set G) := by
      have hsup := Subgroup.coe_mul_of_right_le_normalizer_left Q P0 hP0Q
      rw [← hsup]
      exact hx.2
    rcases hxProd with ⟨q, hq, p0, hp0, hqpx⟩
    have hx_eq : x = q * p0 := hqpx.symm
    have hqP : q ∈ P := by
      have hp0P : p0 ∈ P := hP0P hp0
      have hqpP : q * p0 ∈ P := by
        simpa [← hx_eq] using hx.1
      have hcalc : q = (q * p0) * p0⁻¹ := by
        group
      rw [hcalc]
      exact P.mul_mem hqpP (P.inv_mem hp0P)
    have hqinf : q ∈ P ⊓ Q := ⟨hqP, hq⟩
    have hqbot : q ∈ (⊥ : Subgroup G) := by
      simpa [hPQ] using hqinf
    have hq1 : q = 1 := by
      simpa using hqbot
    simpa [hx_eq, hq1] using hp0
  · intro x hx
    exact ⟨hP0P hx, Subgroup.mem_sup_right hx⟩

/-- Cardinality of the additive group `P = F_{p^q}`. -/
public theorem CFSG.appendixCP_natCard [Fact q.Prime] :
    Nat.card (appendixCP p q) = p ^ q := by
  change Nat.card (Multiplicative (appendixCField p q)) = p ^ q
  rw [Nat.card_congr
    (Multiplicative.ofAdd : appendixCField p q ≃ Multiplicative (appendixCField p q)).symm]
  exact GaloisField.card (p := p) (n := q) (Fact.out : Nat.Prime q).ne_zero

/-- The subgroup `P ≤ PU` is a `p`-group. -/
public theorem CFSG.appendixCPInH_isPGroup [Fact q.Prime] :
    IsPGroup p (appendixCPInH p q) := by
  let hG : IsPGroup p (appendixCP p q) :=
    IsPGroup.of_card (p := p) (G := appendixCP p q) (n := q)
      (appendixCP_natCard (p := p) (q := q))
  have hmap :
      Subgroup.map (SemidirectProduct.inl : appendixCP p q →* appendixCH p q) ⊤ =
        appendixCPInH p q := by
    rw [appendixCPInH]
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, trivial, rfl⟩
  rw [← hmap]
  exact IsPGroup.map (G := appendixCP p q) (K := appendixCH p q)
    (H := ⊤) (hG.to_subgroup (⊤ : Subgroup (appendixCP p q))) SemidirectProduct.inl

/-- The embedded image of `P` is a `p`-group. -/
public theorem CFSG.appendixCEmbedding_CPInH_isPGroup
    {G : Type u} [Group G] [Fact q.Prime] (σ : appendixCH p q →* G) :
    IsPGroup p (Subgroup.map σ (appendixCPInH p q)) := by
  exact IsPGroup.map (G := appendixCH p q) (K := G)
    (H := appendixCPInH p q) (appendixCPInH_isPGroup (p := p) (q := q)) σ

/-- In condition `(B)`, embedded `P` intersects a finite `p'`-subgroup `Q`
trivially. -/
public theorem CFSG.appendixCEmbedding_CPInH_inf_Q_eq_bot_of_coprime_card
    {G : Type u} [Group G] [Fact q.Prime] (σ : appendixCH p q →* G)
    (Q : Subgroup G) [Finite Q] (hcop : Nat.Coprime p (Nat.card Q)) :
    Subgroup.map σ (appendixCPInH p q) ⊓ Q = ⊥ := by
  let Pimg : Subgroup G := Subgroup.map σ (appendixCPInH p q)
  have hP : IsPGroup p Pimg :=
    appendixCEmbedding_CPInH_isPGroup (p := p) (q := q) σ
  have hK : IsPGroup p (Pimg ⊓ Q : Subgroup G) := hP.to_inf_left
  rcases hK.card_eq_or_dvd with hcard | hpdvd
  · exact (Subgroup.eq_bot_iff_card (H := Pimg ⊓ Q)).2 hcard
  · exfalso
    have hdvdQ : Nat.card (Pimg ⊓ Q : Subgroup G) ∣ Nat.card Q :=
      Subgroup.card_dvd_of_le inf_le_right
    have hpnot : ¬ p ∣ Nat.card Q :=
      (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop
    exact hpnot (dvd_trans hpdvd hdvdQ)

/-- Embedded Appendix C Step 3 identity `P ∩ QP₀ = P₀`, where `QP₀` is
represented by `Q ⊔ image(P₀)`. -/
public theorem CFSG.appendixCEmbedding_CPInH_inf_Q_sup_CP0InH_eq_CP0InH_of_coprime_card
    {G : Type u} [Group G] [Fact q.Prime] (σ : appendixCH p q →* G)
    (Q : Subgroup G) [Finite Q] (hcop : Nat.Coprime p (Nat.card Q))
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q) :
    Subgroup.map σ (appendixCPInH p q) ⊓
      (Q ⊔ Subgroup.map σ (appendixCP0InH p q)) =
        Subgroup.map σ (appendixCP0InH p q) := by
  exact appendixC_inf_sup_eq_of_inf_eq_bot_of_le_of_normalizes
    (P := Subgroup.map σ (appendixCPInH p q))
    (Q := Q)
    (P0 := Subgroup.map σ (appendixCP0InH p q))
    (Subgroup.map_mono (appendixCP0InH_le_appendixCPInH (p := p) (q := q)))
    hP0Q
    (appendixCEmbedding_CPInH_inf_Q_eq_bot_of_coprime_card
      (p := p) (q := q) σ Q hcop)

/-- If `A` normalizes `P` and lies in `R`, then, whenever `P ∩ R = P₀`,
`A` normalizes `P₀`. -/
public theorem CFSG.appendixC_normalizes_of_le_normalizer_left_of_le_right_of_inf_eq
    {G : Type u} [Group G] {A P R P0 : Subgroup G}
    (hEq : P ⊓ R = P0)
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hAR : A ≤ R) :
    A ≤ Subgroup.normalizer (P0 : Set G) := by
  intro a ha
  have haRnorm : a ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer (hAR ha)
  have hainf : a ∈ Subgroup.normalizer ((P ⊓ R : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAP ha, haRnorm⟩
  simpa [hEq] using hainf

/-- If `A ≤ P₀` and `y ∈ Q`, then the right-conjugate `A^y` lies in
`Q ⊔ P₀`. -/
public theorem CFSG.appendixCRightConjugate_le_sup_of_le_of_mem
    {G : Type u} [Group G] {A Q P0 : Subgroup G} {y : G}
    (hA : A ≤ P0) (hy : y ∈ Q) :
    appendixCRightConjugate A y ≤ Q ⊔ P0 := by
  intro x hx
  change x ∈ Subgroup.map (MulAut.conj y⁻¹).toMonoidHom A at hx
  rcases hx with ⟨a, ha, rfl⟩
  have haS : a ∈ Q ⊔ P0 := Subgroup.mem_sup_right (hA ha)
  have hyS : y ∈ Q ⊔ P0 := Subgroup.mem_sup_left hy
  have hyinvS : y⁻¹ ∈ Q ⊔ P0 := (Q ⊔ P0).inv_mem hyS
  simpa [MulAut.conj_apply, mul_assoc] using
    (Q ⊔ P0).mul_mem ((Q ⊔ P0).mul_mem hyinvS haS) hyS

/-- The Appendix C right-conjugate `P₁ = P₀^y` lies in `QP₀` whenever
`y ∈ Q`. -/
public theorem CFSG.appendixCEmbedding_rightConjugate_CP0InH_le_Q_sup_CP0InH_of_mem_Q
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    {Q : Subgroup G} {y : G} (hy : y ∈ Q) :
    appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y ≤
      Q ⊔ Subgroup.map σ (appendixCP0InH p q) :=
  appendixCRightConjugate_le_sup_of_le_of_mem (A := Subgroup.map σ (appendixCP0InH p q))
    (Q := Q) (P0 := Subgroup.map σ (appendixCP0InH p q)) (le_refl _) hy

/-- Appendix C Step 3 normalizer transfer: if `P₁ = P₀^y` normalizes embedded
`P`, then it normalizes embedded `P₀`, using `P ∩ QP₀ = P₀`. -/
public theorem CFSG.appendixCEmbedding_rightConjugate_CP0InH_normalizes_CP0InH_of_normalizes_CPInH
    {G : Type u} [Group G] [Fact q.Prime] (σ : appendixCH p q →* G)
    (Q : Subgroup G) [Finite Q] (hcop : Nat.Coprime p (Nat.card Q))
    {y : G} (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hP1P : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCPInH p q))) :
    appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCP0InH p q)) := by
  let Pimg : Subgroup G := Subgroup.map σ (appendixCPInH p q)
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let R : Subgroup G := Q ⊔ P0img
  let P1 : Subgroup G := appendixCRightConjugate P0img y
  have hEq : Pimg ⊓ R = P0img := by
    exact appendixCEmbedding_CPInH_inf_Q_sup_CP0InH_eq_CP0InH_of_coprime_card
      (p := p) (q := q) σ Q hcop hP0Q
  have hP1R : P1 ≤ R :=
    appendixCEmbedding_rightConjugate_CP0InH_le_Q_sup_CP0InH_of_mem_Q
      (p := p) (q := q) σ hy
  exact appendixC_normalizes_of_le_normalizer_left_of_le_right_of_inf_eq
    (A := P1) (P := Pimg) (R := R) (P0 := P0img) hEq hP1P hP1R

/-- The prime-field subgroup `P₀ ≤ P` has order `p`. -/
public theorem CFSG.appendixCP0InP_natCard :
    Nat.card (appendixCP0InP p q) = p := by
  let φ : Multiplicative (ZMod p) →* appendixCP p q :=
    AddMonoidHom.toMultiplicative
      (algebraMap (ZMod p) (appendixCField p q)).toAddMonoidHom
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    apply FaithfulSMul.algebraMap_injective (ZMod p) (appendixCField p q)
    simpa [φ] using congrArg Multiplicative.toAdd hxy
  rw [appendixCP0InP, MonoidHom.range_eq_map]
  calc
    Nat.card (Subgroup.map φ (⊤ : Subgroup (Multiplicative (ZMod p)))) =
        Nat.card (⊤ : Subgroup (Multiplicative (ZMod p))) :=
      Subgroup.card_map_of_injective
        (K := (⊤ : Subgroup (Multiplicative (ZMod p)))) hφinj
    _ = Nat.card (Multiplicative (ZMod p)) := Subgroup.card_top
    _ = p := by simp

/-- The prime-field subgroup `P₀ ≤ H` has order `p`. -/
public theorem CFSG.appendixCP0InH_natCard :
    Nat.card (appendixCP0InH p q) = p := by
  rw [appendixCP0InH]
  calc
    Nat.card (Subgroup.map
        (SemidirectProduct.inl : appendixCP p q →* appendixCH p q)
        (appendixCP0InP p q)) = Nat.card (appendixCP0InP p q) := by
      exact Subgroup.card_map_of_injective
        (K := appendixCP0InP p q)
        (f := (SemidirectProduct.inl : appendixCP p q →* appendixCH p q))
        SemidirectProduct.inl_injective
    _ = p := appendixCP0InP_natCard (p := p) (q := q)

/-- The embedded image of `P₀` has order `p` under an injective ambient embedding. -/
public theorem CFSG.appendixCEmbedding_CP0InH_natCard
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) :
    Nat.card (Subgroup.map σ (appendixCP0InH p q)) = p := by
  calc
    Nat.card (Subgroup.map σ (appendixCP0InH p q)) =
        Nat.card (appendixCP0InH p q) := by
      exact Subgroup.card_map_of_injective
        (K := appendixCP0InH p q) (f := σ) hσ
    _ = p := appendixCP0InH_natCard (p := p) (q := q)

/-- Appendix C source fact `(X)` in the condition-`(B)` witness group, in
Lean's coprime-action language: the fixed points of the `P₀` action on `Q`
meet the action commutator subgroup trivially. -/
public theorem CFSG.appendixCEmbedding_fixedPointSubgroup_inf_commutatorAction_eq_bot
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hcop : Nat.Coprime p (Nat.card Q))
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q) :
    let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
    let φ : P0img →* MulAut Q :=
      Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
    letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
    fixedPointSubgroup P0img Q ⊓ commutatorAction (A := P0img) (G := Q) = ⊥ := by
  classical
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  have : Finite P0img := by
    have hfiniteSet : (P0img : Set G).Finite := by
      change (σ '' ((appendixCP0InH p q : Subgroup (appendixCH p q)) :
        Set (appendixCH p q))).Finite
      exact Set.Finite.image σ (Set.toFinite _)
    exact hfiniteSet.to_subtype
  let φ : P0img →* MulAut Q :=
    Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
  let : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
  have hP0card : Nat.card P0img = p :=
    appendixCEmbedding_CP0InH_natCard (p := p) (q := q) σ hσ
  have hcop' : Nat.Coprime (Nat.card P0img) (Nat.card Q) := by
    simpa [hP0card] using hcop
  have hsolv : Group.IsSolvable Q :=
    Group.isSolvable_of_comm (fun a b => mul_comm' a b)
  have hcompl : IsCompl (fixedPointSubgroup P0img Q)
      (commutatorAction (A := P0img) (G := Q)) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := Q) (A := P0img) hsolv hcop' inferInstance
  exact (disjoint_iff).1 hcompl.disjoint

set_option backward.isDefEq.respectTransparency false in
/-- If the fixed-point component of an element of `Q` is multiplied onto a
commutator-action component, the right conjugate of embedded `P₀` is unchanged.
This is the conjugation part of Appendix C source fact `(XI)`. -/
public theorem CFSG.appendixCEmbedding_rightConjugate_eq_of_fixedPoint_mul
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q) :
    let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
    let φ : P0img →* MulAut Q :=
      Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
    letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
    ∀ f c : Q, f ∈ fixedPointSubgroup P0img Q →
      appendixCRightConjugate P0img ((f : G) * (c : G)) =
        appendixCRightConjugate P0img (c : G) := by
  classical
  dsimp
  intro f c hf
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let φ : P0img →* MulAut Q :=
    Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
  let : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
  change appendixCRightConjugate P0img ((f : G) * (c : G)) =
    appendixCRightConjugate P0img (c : G)
  change f ∈ fixedPointSubgroup P0img Q at hf
  have hf_comm : ∀ a : G, a ∈ P0img → (f : G) * a = a * f := by
    intro a ha
    let a0 : P0img := ⟨a, ha⟩
    have hfix : a0 • f = f :=
      (FixedPoints.mem_subgroup (M := P0img) (a := f)).1 hf a0
    have hval : (a0 : G) * (f : G) * (a0 : G)⁻¹ = (f : G) := by
      simpa [φ, MulAction.compHom_smul_def] using congrArg Subtype.val hfix
    have hmul : a * (f : G) = (f : G) * a := by
      have := congrArg (fun z : G => z * a) hval
      simpa [a0, mul_assoc] using this
    exact hmul.symm
  have hf_conj : ∀ a : G, a ∈ P0img → (f : G)⁻¹ * a * (f : G) = a := by
    intro a ha
    calc
      (f : G)⁻¹ * a * (f : G) = (f : G)⁻¹ * (a * (f : G)) := by rw [mul_assoc]
      _ = (f : G)⁻¹ * ((f : G) * a) := by rw [← hf_comm a ha]
      _ = a := by simp
  ext x
  constructor
  · intro hx
    rw [appendixCRightConjugate, Subgroup.conjBy] at hx ⊢
    rcases hx with ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    change MulAut.conj ((c : G)⁻¹) a =
      MulAut.conj (((f : G) * (c : G))⁻¹) a
    simp [mul_assoc, hf_conj a ha]
  · intro hx
    rw [appendixCRightConjugate, Subgroup.conjBy] at hx ⊢
    rcases hx with ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    change MulAut.conj (((f : G) * (c : G))⁻¹) a =
      MulAut.conj ((c : G)⁻¹) a
    simp [mul_assoc, hf_conj a ha]

/-- Appendix C source fact `(XI)` in condition-`(B)` form. The witness `y ∈ Q`
can be replaced by an element of the action commutator subgroup without
changing the right-conjugate `P₀^y`. -/
public theorem CFSG.appendixCEmbedding_exists_commutatorAction_y_eq_rightConjugate
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hcop : Nat.Coprime p (Nat.card Q))
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    {y : G} (hy : y ∈ Q) :
    let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
    let φ : P0img →* MulAut Q :=
      Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
    letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
    ∃ y' : G, ∃ hy' : y' ∈ Q,
      (⟨y', hy'⟩ : Q) ∈ commutatorAction (A := P0img) (G := Q) ∧
      appendixCRightConjugate P0img y' = appendixCRightConjugate P0img y := by
  classical
  dsimp
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  have : Finite P0img := by
    have hfiniteSet : (P0img : Set G).Finite := by
      change (σ '' ((appendixCP0InH p q : Subgroup (appendixCH p q)) :
        Set (appendixCH p q))).Finite
      exact Set.Finite.image σ (Set.toFinite _)
    exact hfiniteSet.to_subtype
  let φ : P0img →* MulAut Q :=
    Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
  let : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
  have hP0card : Nat.card P0img = p :=
    appendixCEmbedding_CP0InH_natCard (p := p) (q := q) σ hσ
  have hcop' : Nat.Coprime (Nat.card P0img) (Nat.card Q) := by
    simpa [hP0card] using hcop
  have hsolv : Group.IsSolvable Q :=
    Group.isSolvable_of_comm (fun a b => mul_comm' a b)
  have hcompl : IsCompl (fixedPointSubgroup P0img Q)
      (commutatorAction (A := P0img) (G := Q)) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := Q) (A := P0img) hsolv hcop' inferInstance
  let yQ : Q := ⟨y, hy⟩
  have hySup :
      yQ ∈ fixedPointSubgroup P0img Q ⊔ commutatorAction (A := P0img) (G := Q) := by
    simp [hcompl.sup_eq_top]
  let : CommGroup Q := IsMulCommutative.instCommGroup
  rw [Subgroup.mem_sup] at hySup
  rcases hySup with ⟨f, hf, c, hc, hfc⟩
  refine ⟨(c : G), c.property, hc, ?_⟩
  have hfcG : (f : G) * (c : G) = y :=
    congrArg Subtype.val hfc
  have hright : appendixCRightConjugate P0img ((f : G) * (c : G)) =
      appendixCRightConjugate P0img (c : G) := by
    simpa [P0img, φ] using
      appendixCEmbedding_rightConjugate_eq_of_fixedPoint_mul
        (p := p) (q := q) σ Q hP0Q f c hf
  rw [hfcG] at hright
  exact hright.symm

/-- Source `(XI)` with the normalizer hypothesis transported to the
commutator-action representative of `y`. -/
public theorem CFSG.appendixCEmbedding_exists_commutatorAction_y_with_normalizes
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hcop : Nat.Coprime p (Nat.card Q))
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    {y : G} (hy : y ∈ Q)
    (hP1U : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCUInH p q))) :
    let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
    let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
    let φ : P0img →* MulAut Q :=
      Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
    letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
    ∃ y' : G, ∃ hy' : y' ∈ Q,
      (⟨y', hy'⟩ : Q) ∈ commutatorAction (A := P0img) (G := Q) ∧
      appendixCNormalizes (appendixCRightConjugate P0img y') Uimg ∧
      appendixCRightConjugate P0img y' = appendixCRightConjugate P0img y := by
  classical
  dsimp
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
  let φ : P0img →* MulAut Q :=
    Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
  let : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
  rcases appendixCEmbedding_exists_commutatorAction_y_eq_rightConjugate
      (p := p) (q := q) σ hσ Q hcop hP0Q hy with
    ⟨y', hy', hycomm, hyconj⟩
  refine ⟨y', hy', hycomm, ?_, hyconj⟩
  change appendixCNormalizes (appendixCRightConjugate P0img y') Uimg
  simpa [P0img, Uimg, hyconj] using hP1U

/-- Condition `(B)` can be witnessed with `y` already lying in the
commutator-action subgroup `[Q, P₀]`, while also exposing source fact `(X)`.
This packages the action-theoretic setup for the remaining Step 4 calculation. -/
public theorem CFSG.appendixCConditionB_exists_commutatorAction_y
    (hB : appendixCConditionB.{u} p q) :
    ∃ G : Type u, ∃ _ : Group G, ∃ σ : appendixCH p q →* G,
      Function.Injective σ ∧
      ∃ Q : Subgroup G, ∃ _ : Finite Q, ∃ _ : IsMulCommutative Q,
        Nat.Coprime p (Nat.card Q) ∧
        ∃ y : G, ∃ hy : y ∈ Q,
          ∃ hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q,
            let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
            let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
            let φ : P0img →* MulAut Q :=
              Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
            letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
            fixedPointSubgroup P0img Q ⊓
              commutatorAction (A := P0img) (G := Q) = ⊥ ∧
            (⟨y, hy⟩ : Q) ∈ commutatorAction (A := P0img) (G := Q) ∧
            appendixCNormalizes (appendixCRightConjugate P0img y) Uimg := by
  classical
  rcases hB with ⟨G, hG, σ, hσ, Q, hQfin, hQcomm, hcop, y, hy, hP0Q, hP1U⟩
  let : Group G := hG
  let : Finite Q := hQfin
  let : IsMulCommutative Q := hQcomm
  rcases appendixCEmbedding_exists_commutatorAction_y_with_normalizes
      (p := p) (q := q) σ hσ Q hcop hP0Q hy hP1U with
    ⟨y', hy', hycomm, hP1U', _hyconj⟩
  have hfixed :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      fixedPointSubgroup P0img Q ⊓ commutatorAction (A := P0img) (G := Q) = ⊥ :=
    appendixCEmbedding_fixedPointSubgroup_inf_commutatorAction_eq_bot
      (p := p) (q := q) σ hσ Q hcop hP0Q
  refine ⟨G, hG, σ, hσ, Q, hQfin, hQcomm, hcop, y', hy', hP0Q, ?_⟩
  dsimp
  exact ⟨hfixed, hycomm, hP1U'⟩

/-- The abstract norm-one subgroup `U` is multiplicatively equivalent to its
copy inside the Appendix C semidirect product `H = PU`. -/
public def CFSG.appendixCUInHEquiv :
    appendixCNormOneUnits p q ≃* appendixCUInH p q := by
  let e0 : (⊤ : Subgroup (appendixCNormOneUnits p q)) ≃*
      Subgroup.map (SemidirectProduct.inr :
        appendixCNormOneUnits p q →* appendixCH p q) ⊤ :=
    Subgroup.equivMapOfInjective
      (⊤ : Subgroup (appendixCNormOneUnits p q))
      (SemidirectProduct.inr : appendixCNormOneUnits p q →* appendixCH p q)
      SemidirectProduct.inr_injective
  let eTop : appendixCNormOneUnits p q ≃*
      (⊤ : Subgroup (appendixCNormOneUnits p q)) :=
    (Subgroup.topEquiv :
      (⊤ : Subgroup (appendixCNormOneUnits p q)) ≃*
        appendixCNormOneUnits p q).symm
  have hmap :
      Subgroup.map
          (SemidirectProduct.inr :
            appendixCNormOneUnits p q →* appendixCH p q)
          (⊤ : Subgroup (appendixCNormOneUnits p q)) =
        appendixCUInH p q := by
    rw [← MonoidHom.range_eq_map]
    rfl
  exact (eTop.trans e0).trans (MulEquiv.subgroupCongr hmap)

/-- The equivalence `appendixCUInHEquiv` is the right injection on values. -/
public theorem CFSG.appendixCUInHEquiv_apply (u : appendixCNormOneUnits p q) :
    ((appendixCUInHEquiv (p := p) (q := q) u : appendixCUInH p q) :
      appendixCH p q) = SemidirectProduct.inr u := by
  simp [appendixCUInHEquiv]

/-- The abstract norm-one subgroup `U` is equivalent to its embedded image in
any condition-`(B)` ambient group. -/
public def CFSG.appendixCEmbedding_CUInHEquiv
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) :
    appendixCNormOneUnits p q ≃* Subgroup.map σ (appendixCUInH p q) :=
  (appendixCUInHEquiv (p := p) (q := q)).trans
    (Subgroup.equivMapOfInjective (appendixCUInH p q) σ hσ)

/-- The embedded `U` equivalence is the composite of the right injection with
the ambient embedding. -/
public theorem CFSG.appendixCEmbedding_CUInHEquiv_apply
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) (u : appendixCNormOneUnits p q) :
    ((appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ u :
      Subgroup.map σ (appendixCUInH p q)) : G) =
        σ (SemidirectProduct.inr u) := by
  simp [appendixCEmbedding_CUInHEquiv, appendixCUInHEquiv_apply]

/-- Recover the abstract norm-one unit represented by an embedded `U` element. -/
public theorem CFSG.appendixCEmbedding_CUInHEquiv_symm_apply
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {u0 : G}
    (hu : u0 ∈ Subgroup.map σ (appendixCUInH p q)) :
    σ (SemidirectProduct.inr
      ((appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ).symm
        ⟨u0, hu⟩)) = u0 := by
  let e : appendixCNormOneUnits p q ≃* Subgroup.map σ (appendixCUInH p q) :=
    appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ
  have happly := appendixCEmbedding_CUInHEquiv_apply
    (p := p) (q := q) σ hσ (e.symm ⟨u0, hu⟩)
  have hleft : ((e (e.symm ⟨u0, hu⟩) :
      Subgroup.map σ (appendixCUInH p q)) : G) = u0 := by
    simp [e]
  rw [← happly]
  exact hleft

/-- A normalizer element of the embedded `U` induces a multiplicative
automorphism of the abstract norm-one subgroup. This is the formal action
underlying the Step 4 conjugation by powers of `t`. -/
public def CFSG.appendixCEmbedding_conjNormOneUnitsMulEquiv
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {t : G} (htnorm : t ∈ Subgroup.normalizer
      (Subgroup.map σ (appendixCUInH p q) : Set G)) :
    appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q := by
  let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
  let e : appendixCNormOneUnits p q ≃* Uimg :=
    appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ
  exact (e.trans (Uimg.normalizerMonoidHom ⟨t, htnorm⟩)).trans e.symm

/-- Value formula for the normalizer-induced automorphism of `U`. -/
public theorem CFSG.appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {t : G} (htnorm : t ∈ Subgroup.normalizer
      (Subgroup.map σ (appendixCUInH p q) : Set G))
    (u : appendixCNormOneUnits p q) :
    σ (SemidirectProduct.inr
      (appendixCEmbedding_conjNormOneUnitsMulEquiv
        (p := p) (q := q) σ hσ htnorm u)) =
      t * σ (SemidirectProduct.inr u) * t⁻¹ := by
  let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
  let e : appendixCNormOneUnits p q ≃* Uimg :=
    appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ
  have hval : ((e (appendixCEmbedding_conjNormOneUnitsMulEquiv
      (p := p) (q := q) σ hσ htnorm u) : Uimg) : G) =
      t * ((e u : Uimg) : G) * t⁻¹ := by
    change
      ((e (((e.trans (Uimg.normalizerMonoidHom ⟨t, htnorm⟩)).trans e.symm) u) :
        Uimg) : G) = _
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have he_apply (v : appendixCNormOneUnits p q) :
      ((e v : Uimg) : G) = σ (SemidirectProduct.inr v) := by
    exact appendixCEmbedding_CUInHEquiv_apply (p := p) (q := q) σ hσ v
  rw [he_apply, he_apply] at hval
  exact hval

/-- Value formula for the inverse of the normalizer-induced automorphism of
`U`. This is the right-conjugation convention used in the source C4 product. -/
public theorem CFSG.appendixCEmbedding_conjNormOneUnitsMulEquiv_symm_apply
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {t : G} (htnorm : t ∈ Subgroup.normalizer
      (Subgroup.map σ (appendixCUInH p q) : Set G))
    (u : appendixCNormOneUnits p q) :
    σ (SemidirectProduct.inr
      ((appendixCEmbedding_conjNormOneUnitsMulEquiv
        (p := p) (q := q) σ hσ htnorm).symm u)) =
      t⁻¹ * σ (SemidirectProduct.inr u) * t := by
  let Tunit : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q) σ hσ htnorm
  have happly := appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
    (p := p) (q := q) σ hσ htnorm (Tunit.symm u)
  have hforward :
      σ (SemidirectProduct.inr u) =
        t * σ (SemidirectProduct.inr (Tunit.symm u)) * t⁻¹ := by
    simpa [Tunit] using happly
  have h := congrArg (fun g : G => t⁻¹ * g * t) hforward
  group at h
  simpa [Tunit] using h.symm

/-- Value formula for the normalizer-induced automorphism, starting from an
arbitrary embedded `U` element rather than a named norm-one unit. -/
public theorem CFSG.appendixCEmbedding_conjNormOneUnitsMulEquiv_apply_of_mem
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {t u0 : G}
    (htnorm : t ∈ Subgroup.normalizer
      (Subgroup.map σ (appendixCUInH p q) : Set G))
    (hu : u0 ∈ Subgroup.map σ (appendixCUInH p q)) :
    σ (SemidirectProduct.inr
      (appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
        σ hσ htnorm
        ((appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ).symm
          ⟨u0, hu⟩))) =
      t * u0 * t⁻¹ := by
  have happly := appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
    (p := p) (q := q) σ hσ htnorm
    ((appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ).symm ⟨u0, hu⟩)
  simpa [appendixCEmbedding_CUInHEquiv_symm_apply
    (p := p) (q := q) σ hσ hu] using happly


/-- Conjugating the embedded `U` by `t⁻¹` induces the inverse of the
normalizer-induced automorphism coming from conjugation by `t`. -/
public theorem CFSG.appendixCEmbedding_conjNormOneUnitsMulEquiv_inv_eq_symm
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {t : G}
    (htnorm : t ∈ Subgroup.normalizer
      (Subgroup.map σ (appendixCUInH p q) : Set G))
    (htnorm_inv : t⁻¹ ∈ Subgroup.normalizer
      (Subgroup.map σ (appendixCUInH p q) : Set G)) :
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
        σ hσ htnorm_inv =
      (appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
        σ hσ htnorm).symm := by
  apply MulEquiv.ext
  intro u
  have hinj : Function.Injective
      (fun v : appendixCNormOneUnits p q => σ (SemidirectProduct.inr v)) := by
    intro v w hvw
    have hpre : (SemidirectProduct.inr v : appendixCH p q) =
        SemidirectProduct.inr w := hσ hvw
    have hright := congrArg (fun x : appendixCH p q => x.right) hpre
    simpa using hright
  apply hinj
  calc
    σ (SemidirectProduct.inr
        (appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
          σ hσ htnorm_inv u))
        = t⁻¹ * σ (SemidirectProduct.inr u) * (t⁻¹)⁻¹ := by
          exact appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
            (p := p) (q := q) σ hσ htnorm_inv u
    _ = t⁻¹ * σ (SemidirectProduct.inr u) * t := by group
    _ = σ (SemidirectProduct.inr
        ((appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
          σ hσ htnorm).symm u)) := by
          exact (appendixCEmbedding_conjNormOneUnitsMulEquiv_symm_apply
            (p := p) (q := q) σ hσ htnorm u).symm

/-- Iterating the normalizer-induced automorphism is conjugation by the
corresponding power of the normalizing element. -/
public theorem CFSG.appendixCEmbedding_conjNormOneUnitsMulEquiv_iterate_apply
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {t : G} (htnorm : t ∈ Subgroup.normalizer
      (Subgroup.map σ (appendixCUInH p q) : Set G))
    (u : appendixCNormOneUnits p q) :
    ∀ n : ℕ,
      σ (SemidirectProduct.inr
        (((appendixCEmbedding_conjNormOneUnitsMulEquiv
            (p := p) (q := q) σ hσ htnorm :
            appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[n]) u)) =
        t ^ n * σ (SemidirectProduct.inr u) * (t ^ n)⁻¹ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [appendixCEmbedding_conjNormOneUnitsMulEquiv_apply]
      rw [ih]
      rw [pow_succ]
      group

/-- If the normalizing element has order dividing `p`, then the induced
automorphism of `U` has `p`th iterate equal to the identity. -/
public theorem CFSG.appendixCEmbedding_conjNormOneUnitsMulEquiv_pow
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {t : G} (htnorm : t ∈ Subgroup.normalizer
      (Subgroup.map σ (appendixCUInH p q) : Set G))
    (htpow : t ^ p = 1) (u : appendixCNormOneUnits p q) :
    ((appendixCEmbedding_conjNormOneUnitsMulEquiv
        (p := p) (q := q) σ hσ htnorm :
        appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[p]) u = u := by
  let e : appendixCNormOneUnits p q ≃* Subgroup.map σ (appendixCUInH p q) :=
    appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ
  apply e.injective
  apply Subtype.ext
  have hiter := appendixCEmbedding_conjNormOneUnitsMulEquiv_iterate_apply
    (p := p) (q := q) σ hσ htnorm u p
  have hleft :
      ((e (((appendixCEmbedding_conjNormOneUnitsMulEquiv
          (p := p) (q := q) σ hσ htnorm :
          appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[p]) u) :
        Subgroup.map σ (appendixCUInH p q)) : G) =
      σ (SemidirectProduct.inr (((appendixCEmbedding_conjNormOneUnitsMulEquiv
          (p := p) (q := q) σ hσ htnorm :
          appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[p]) u)) := by
    exact appendixCEmbedding_CUInHEquiv_apply (p := p) (q := q) σ hσ _
  rw [hleft]
  rw [hiter]
  simp [htpow, e, appendixCEmbedding_CUInHEquiv_apply]

/-- Elements of the right-conjugate `P₁ = P₀^y` have `p`th power one. -/
public theorem CFSG.appendixCEmbedding_rightConjugate_mem_pow_prime_eq_one
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {y t : G}
    (ht : t ∈ appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y) :
    t ^ p = 1 := by
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let P1 : Subgroup G := appendixCRightConjugate P0img y
  have hP0card : Nat.card P0img = p :=
    appendixCEmbedding_CP0InH_natCard (p := p) (q := q) σ hσ
  have hP1card : Nat.card P1 = p := by
    calc
      Nat.card P1 = Nat.card P0img := by
        change Nat.card (appendixCRightConjugate P0img y) = Nat.card P0img
        rw [appendixCRightConjugate, Subgroup.conjBy]
        exact Subgroup.card_map_of_injective
          (K := P0img) (f := (MulAut.conj y⁻¹).toMonoidHom)
          (MulAut.conj y⁻¹).injective
      _ = p := hP0card
  have : Finite P1 := Nat.finite_of_card_ne_zero (by
    rw [hP1card]
    exact (Fact.out : Nat.Prime p).pos.ne')
  have : Fintype P1 := Fintype.ofFinite P1
  let tg : P1 := ⟨t, by simpa [P1, P0img] using ht⟩
  have hcard : Fintype.card P1 = p := by
    rw [Fintype.card_eq_nat_card, hP1card]
  have hpow_sub : tg ^ Fintype.card P1 = 1 := pow_card_eq_one
  have hpow_sub_p : tg ^ p = 1 := by
    simpa [hcard] using hpow_sub
  exact congrArg Subtype.val hpow_sub_p

/-- The Step 4 automorphism induced by conjugation by `t^3` has `p`th iterate
equal to the identity whenever `t ∈ P₀^y`. -/
public theorem CFSG.appendixCEmbedding_conjNormOneUnitsMulEquiv_pow_of_rightConjugate
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ) {y t : G}
    (hP1U : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCUInH p q)))
    (ht : t ∈ appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y)
    (u : appendixCNormOneUnits p q) :
    ((appendixCEmbedding_conjNormOneUnitsMulEquiv
        (p := p) (q := q) σ hσ
        ((Subgroup.normalizer (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
          (hP1U ht) 3) :
        appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[p]) u = u := by
  have htpow : t ^ p = 1 :=
    appendixCEmbedding_rightConjugate_mem_pow_prime_eq_one
      (p := p) (q := q) σ hσ ht
  have ht3pow : (t ^ 3) ^ p = 1 := by
    rw [← pow_mul t 3 p, Nat.mul_comm 3 p, pow_mul, htpow, one_pow]
  exact appendixCEmbedding_conjNormOneUnitsMulEquiv_pow
    (p := p) (q := q) σ hσ
    ((Subgroup.normalizer (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
      (hP1U ht) 3) ht3pow u

/-- If a nontrivial element generates a prime-order action group, then an
element of the action commutator subgroup fixed by that generator is trivial,
provided source fact `(X)` holds. This is the local form of the Step 4 sentence
that an element of `[Q,P₀]` fixed by `s⁻¹` must be `1`. -/
public theorem CFSG.appendixC_commutatorAction_eq_one_of_fixed_by_nontrivial_generator
    {A : Type u} {G : Type v} [Group A] [Group G] [MulDistribMulAction A G]
    {r : ℕ} [Fact r.Prime] (hcard : Nat.card A = r)
    (hfixedInf : fixedPointSubgroup A G ⊓ commutatorAction (A := A) (G := G) = ⊥)
    {a : A} (ha : a ≠ 1) {x : G}
    (hxcomm : x ∈ commutatorAction (A := A) (G := G))
    (hfix : a • x = x) :
    x = 1 := by
  have hxfix : x ∈ fixedPointSubgroup A G := by
    rw [FixedPoints.mem_subgroup]
    intro b
    let Fx : Subgroup A := fixingSubgroup A ({x} : Set G)
    have haFx : a ∈ Fx := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      simp at hy
      simpa [hy] using hfix
    have hle : Subgroup.zpowers a ≤ Fx := Subgroup.zpowers_le_of_mem haFx
    have hb : b ∈ Subgroup.zpowers a :=
      mem_zpowers_of_prime_card (G := A) hcard ha
    have hbFx : b ∈ Fx := hle hb
    exact (mem_fixingSubgroup_iff A (s := ({x} : Set G)) (m := b)).1 hbFx x
      (by simp)
  have hxinf : x ∈ fixedPointSubgroup A G ⊓ commutatorAction (A := A) (G := G) :=
    ⟨hxfix, hxcomm⟩
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hfixedInf] using hxinf
  simpa using hxbot

set_option backward.isDefEq.respectTransparency false in
/-- Condition-`(B)` embedded form of the fixed-point/commutator endpoint:
an element of `[Q,P₀]` fixed by a nontrivial embedded `P₀` element is trivial.
This packages the source use of `(X)` after the C10 modulo-`Q` calculation. -/
public theorem CFSG.appendixCEmbedding_commutatorAction_eq_one_of_fixed_by_P0
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hfixed :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      fixedPointSubgroup P0img Q ⊓ commutatorAction (A := P0img) (G := Q) = ⊥)
    {a x : G}
    (ha : a ∈ Subgroup.map σ (appendixCP0InH p q)) (ha_ne : a ≠ 1)
    (hx : x ∈ Q)
    (hxcomm :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      (⟨x, hx⟩ : Q) ∈ commutatorAction (A := P0img) (G := Q))
    (hfix : a * x * a⁻¹ = x) :
    x = 1 := by
  classical
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let φ : P0img →* MulAut Q :=
    Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
  let : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
  let a0 : P0img := ⟨a, by simpa [P0img] using ha⟩
  let x0 : Q := ⟨x, hx⟩
  have ha0_ne : a0 ≠ 1 := by
    intro h
    exact ha_ne (congrArg Subtype.val h)
  have hfix0 : a0 • x0 = x0 := by
    apply Subtype.ext
    simpa [a0, x0, φ, MulAction.compHom_smul_def] using hfix
  have hxcomm0 : x0 ∈ commutatorAction (A := P0img) (G := Q) := by
    simpa [P0img, φ, x0] using hxcomm
  have hfixed0 :
      fixedPointSubgroup P0img Q ⊓ commutatorAction (A := P0img) (G := Q) = ⊥ := by
    simpa [P0img, φ] using hfixed
  have hcard : Nat.card P0img = p := by
    simpa [P0img] using
      appendixCEmbedding_CP0InH_natCard (p := p) (q := q) σ hσ
  have hx0_one : x0 = 1 :=
    appendixC_commutatorAction_eq_one_of_fixed_by_nontrivial_generator
      (A := P0img) (G := Q) (r := p) hcard hfixed0 ha0_ne hxcomm0 hfix0
  exact congrArg Subtype.val hx0_one

/-- Right-conjugation preserves subgroup cardinality. -/
public theorem CFSG.appendixCRightConjugate_natCard
    {G : Type u} [Group G] (A : Subgroup G) (y : G) :
    Nat.card (appendixCRightConjugate A y) = Nat.card A := by
  rw [appendixCRightConjugate, Subgroup.conjBy]
  exact Subgroup.card_map_of_injective
    (K := A) (f := (MulAut.conj y⁻¹).toMonoidHom)
    (MulAut.conj y⁻¹).injective

/-- If `P₀` normalizes `Q` and `Q ∩ P₀ = 1`, then `|QP₀| = |Q| * |P₀|`. -/
public theorem CFSG.appendixC_sup_natCard_eq_mul_of_inf_eq_bot_of_le_normalizer
    {G : Type u} [Group G] {Q P0 : Subgroup G}
    (hP0Q : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hinf : Q ⊓ P0 = ⊥) :
    Nat.card (Q ⊔ P0 : Subgroup G) = Nat.card Q * Nat.card P0 := by
  let R : Subgroup G := P0 ⊔ Q
  let Qs : Subgroup R := Q.subgroupOf R
  let P0s : Subgroup R := P0.subgroupOf R
  have : Qs.Normal := by
    simpa [R, Qs] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := P0) (N := Q) hP0Q)
  have hcomp : Qs.IsComplement' P0s := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxQ hxP0
      apply Subtype.ext
      have hxinf : ((x : R) : G) ∈ Q ⊓ P0 := ⟨hxQ, hxP0⟩
      have hxbot : ((x : R) : G) ∈ (⊥ : Subgroup G) := by
        simpa [hinf] using hxinf
      simpa using hxbot
    · rw [Set.eq_univ_iff_forall]
      intro x
      have htop : Qs ⊔ P0s = ⊤ := by
        calc
          Qs ⊔ P0s = (Q ⊔ P0).subgroupOf R := by
            symm
            simpa [R, Qs, P0s] using
              (Subgroup.subgroupOf_sup (A := Q) (A' := P0) (B := R)
                le_sup_right le_sup_left)
          _ = ⊤ := by
            exact Subgroup.subgroupOf_eq_top.mpr (by simp [R, sup_comm])
      have hx_top : x ∈ Qs ⊔ P0s := by simp [htop]
      rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := Qs) (t := P0s)).1
          hx_top with
        ⟨q, hqQ, p0, hp0P0, hmul⟩
      exact ⟨q, hqQ, p0, hp0P0, hmul⟩
  have hmul := hcomp.card_mul_card
  have hQcard : Nat.card Qs = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Q) (K := R)
      le_sup_right).toEquiv
  have hP0card : Nat.card P0s = Nat.card P0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := P0) (K := R)
      le_sup_left).toEquiv
  have hR : Nat.card R = Nat.card Q * Nat.card P0 := by
    simpa [R, Qs, P0s, hQcard, hP0card, mul_comm] using hmul.symm
  simpa [R, sup_comm] using hR

/-- Sylow/cardinality core for Appendix C Step 3. If `P₀` and `P₁` both have
order `p`, `P₁ ≤ QP₀`, and `P₁` normalizes `P₀`, then the coprime `Q` factor
forces `P₁ = P₀`. -/
public theorem CFSG.appendixC_prime_order_subgroup_eq_of_le_sup_of_normalizes
    {G : Type u} [Group G] {Q P0 P1 : Subgroup G} [Finite Q]
    (hcop : Nat.Coprime p (Nat.card Q))
    (hP0card : Nat.card P0 = p)
    (hP1card : Nat.card P1 = p)
    (hP0Q : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hinf : Q ⊓ P0 = ⊥)
    (hP1R : P1 ≤ Q ⊔ P0)
    (hP1P0 : P1 ≤ Subgroup.normalizer (P0 : Set G)) :
    P1 = P0 := by
  let R : Subgroup G := Q ⊔ P0
  let S : Subgroup G := P1 ⊔ P0
  have hRcard : Nat.card R = Nat.card Q * p := by
    dsimp [R]
    rw [appendixC_sup_natCard_eq_mul_of_inf_eq_bot_of_le_normalizer hP0Q hinf,
      hP0card]
  have hRcard_ne_zero : Nat.card R ≠ 0 := by
    rw [hRcard]
    exact mul_ne_zero (Nat.card_pos (α := Q)).ne'
      (Fact.out : Nat.Prime p).pos.ne'
  have : Finite R := Nat.finite_of_card_ne_zero hRcard_ne_zero
  have hSR : S ≤ R := by
    exact sup_le hP1R le_sup_right
  have hSdvdR : Nat.card S ∣ Nat.card R := Subgroup.card_dvd_of_le hSR
  have hScard_ne_zero : Nat.card S ≠ 0 := by
    intro hzero
    rw [hzero] at hSdvdR
    exact hRcard_ne_zero (by simpa using hSdvdR)
  have : Finite S := Nat.finite_of_card_ne_zero hScard_ne_zero
  have : Finite P0 := Nat.finite_of_card_ne_zero (by
    rw [hP0card]
    exact (Fact.out : Nat.Prime p).pos.ne')
  have hP0p : IsPGroup p P0 := by
    apply IsPGroup.of_card (p := p) (G := P0) (n := 1)
    simpa [pow_one] using hP0card
  have hP1p : IsPGroup p P1 := by
    apply IsPGroup.of_card (p := p) (G := P1) (n := 1)
    simpa [pow_one] using hP1card
  have hSp : IsPGroup p S := by
    exact IsPGroup.to_sup_of_normal_right' (G := G) (H := P1) (K := P0)
      hP1p hP0p hP1P0
  rcases (IsPGroup.iff_card (p := p) (G := S)).1 hSp with ⟨n, hnS⟩
  have hp_dvd_cardS : p ∣ Nat.card S := by
    rw [← hP0card]
    exact Subgroup.card_dvd_of_le (show P0 ≤ S from le_sup_right)
  have hn_pos : 0 < n := by
    by_contra hnnot
    have hn0 : n = 0 := by omega
    have hp_dvd_one : p ∣ 1 := by
      simpa [hnS, hn0] using hp_dvd_cardS
    exact (Fact.out : Nat.Prime p).not_dvd_one hp_dvd_one
  have hn_le_one : n ≤ 1 := by
    by_contra hnnot
    have h2n : 2 ≤ n := by omega
    have hp2_dvd_cardS : p ^ 2 ∣ Nat.card S := by
      rw [hnS]
      exact pow_dvd_pow p h2n
    have hp2_dvd_R : p ^ 2 ∣ Nat.card R := dvd_trans hp2_dvd_cardS hSdvdR
    have hp2_dvd_Qp : p ^ 2 ∣ Nat.card Q * p := by
      simpa [hRcard] using hp2_dvd_R
    have hp_dvd_Q : p ∣ Nat.card Q := by
      have hp2_dvd_Qp' : p * p ∣ Nat.card Q * p := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hp2_dvd_Qp
      exact (Nat.mul_dvd_mul_iff_right (Fact.out : Nat.Prime p).pos).1
        hp2_dvd_Qp'
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop) hp_dvd_Q
  have hn1 : n = 1 := by omega
  have hScard : Nat.card S = p := by
    simpa [hn1, pow_one] using hnS
  have hS_eq_P0 : S = P0 := by
    exact (Subgroup.eq_of_le_of_card_ge (show P0 ≤ S from le_sup_right)
      (by rw [hScard, hP0card])).symm
  have hP1_le_P0 : P1 ≤ P0 := by
    intro x hx
    have hxS : x ∈ S := (show P1 ≤ S from le_sup_left) hx
    simpa [hS_eq_P0] using hxS
  exact Subgroup.eq_of_le_of_card_ge hP1_le_P0 (by rw [hP1card, hP0card])

/-- Condition `(B)` specialization of the Sylow/cardinality step: once
`P₁ = P₀^y` normalizes embedded `P₀`, it must equal embedded `P₀`. -/
public theorem CFSG.appendixCEmbedding_rightConjugate_CP0InH_eq_CP0InH_of_normalizes_CP0InH
    {G : Type u} [Group G] [Fact q.Prime] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] (hcop : Nat.Coprime p (Nat.card Q))
    {y : G} (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hP1P0 : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCP0InH p q))) :
    appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y =
      Subgroup.map σ (appendixCP0InH p q) := by
  let Pimg : Subgroup G := Subgroup.map σ (appendixCPInH p q)
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let P1 : Subgroup G := appendixCRightConjugate P0img y
  have hP0card : Nat.card P0img = p :=
    appendixCEmbedding_CP0InH_natCard (p := p) (q := q) σ hσ
  have hP1card : Nat.card P1 = p := by
    calc
      Nat.card P1 = Nat.card P0img := appendixCRightConjugate_natCard P0img y
      _ = p := hP0card
  have hPinfQ : Pimg ⊓ Q = ⊥ :=
    appendixCEmbedding_CPInH_inf_Q_eq_bot_of_coprime_card
      (p := p) (q := q) σ Q hcop
  have hQinfP0 : Q ⊓ P0img = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxPinfQ : x ∈ Pimg ⊓ Q := by
        constructor
        · exact Subgroup.map_mono
            (appendixCP0InH_le_appendixCPInH (p := p) (q := q)) hx.2
        · exact hx.1
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [hPinfQ] using hxPinfQ
      simpa using hxbot
    · exact bot_le
  have hP1R : P1 ≤ Q ⊔ P0img :=
    appendixCEmbedding_rightConjugate_CP0InH_le_Q_sup_CP0InH_of_mem_Q
      (p := p) (q := q) σ hy
  exact appendixC_prime_order_subgroup_eq_of_le_sup_of_normalizes
    (p := p) (Q := Q) (P0 := P0img) (P1 := P1)
    hcop hP0card hP1card hP0Q hQinfP0 hP1R hP1P0

/-- Condition `(B)` specialization of the full source Sylow sentence: if
`P₁` normalizes embedded `P`, then the previous normalizer-transfer step and
the Sylow/cardinality step give `P₁ = P₀`. -/
public theorem CFSG.appendixCEmbedding_rightConjugate_CP0InH_eq_CP0InH_of_normalizes_CPInH
    {G : Type u} [Group G] [Fact q.Prime] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] (hcop : Nat.Coprime p (Nat.card Q))
    {y : G} (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hP1P : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCPInH p q))) :
    appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y =
      Subgroup.map σ (appendixCP0InH p q) := by
  have hP1P0 :
      appendixCNormalizes
        (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
        (Subgroup.map σ (appendixCP0InH p q)) :=
    appendixCEmbedding_rightConjugate_CP0InH_normalizes_CP0InH_of_normalizes_CPInH
      (p := p) (q := q) σ Q hcop hy hP0Q hP1P
  exact appendixCEmbedding_rightConjugate_CP0InH_eq_CP0InH_of_normalizes_CP0InH
    (p := p) (q := q) σ hσ Q hcop hy hP0Q hP1P0

/-- Normalizer containment reflects along an injective embedding. -/
public theorem CFSG.appendixCEmbedding_normalizes_reflect_of_injective
    {H : Type v} {G : Type u} [Group H] [Group G] {A B : Subgroup H}
    (σ : H →* G) (hσ : Function.Injective σ)
    (h : appendixCNormalizes (Subgroup.map σ A) (Subgroup.map σ B)) :
    appendixCNormalizes A B := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have ha_img : σ a ∈ Subgroup.map σ A := ⟨a, ha, rfl⟩
    have hb_img : σ b ∈ Subgroup.map σ B := ⟨b, hb, rfl⟩
    have hconj_img : σ a * σ b * (σ a)⁻¹ ∈ Subgroup.map σ B :=
      (Subgroup.mem_normalizer_iff.mp (h ha_img) (σ b)).1 hb_img
    rcases hconj_img with ⟨c, hcB, hc_eq⟩
    have hpre : a * b * a⁻¹ = c := by
      apply hσ
      simpa [map_mul] using hc_eq.symm
    simpa [hpre] using hcB
  · intro hconj
    have ha_img : σ a ∈ Subgroup.map σ A := ⟨a, ha, rfl⟩
    have hconj_img : σ a * σ b * (σ a)⁻¹ ∈ Subgroup.map σ B := by
      refine ⟨a * b * a⁻¹, hconj, ?_⟩
      simp [map_mul]
    have hb_img : σ b ∈ Subgroup.map σ B :=
      (Subgroup.mem_normalizer_iff.mp (h ha_img) (σ b)).2 hconj_img
    rcases hb_img with ⟨c, hcB, hc_eq⟩
    have hb_eq : b = c := by
      apply hσ
      simpa using hc_eq.symm
    simpa [hb_eq] using hcB

/-- In the Appendix C model, a nontrivial norm-one unit prevents `P₀` from
normalizing `U`. -/
public theorem CFSG.appendixCP0InH_not_normalizes_CUInH_of_nontrivial_normOneUnit
    {u : appendixCNormOneUnits p q} (hu : u ≠ 1) :
    ¬ appendixCNormalizes (appendixCP0InH p q) (appendixCUInH p q) := by
  intro hnorm
  let s : appendixCH p q :=
    SemidirectProduct.inl (Multiplicative.ofAdd (1 : appendixCField p q))
  let uH : appendixCH p q := SemidirectProduct.inr u
  have hs : s ∈ appendixCP0InH p q := by
    rw [appendixCP0InH_mem_iff]
    refine ⟨1, ?_⟩
    simp [s]
  have huH : uH ∈ appendixCUInH p q := by
    rw [appendixCUInH_mem_iff]
    exact ⟨u, rfl⟩
  have hs_norm : s ∈
      Subgroup.normalizer (appendixCUInH p q : Set (appendixCH p q)) :=
    hnorm hs
  have hconj : s * uH * s⁻¹ ∈ appendixCUInH p q :=
    (Subgroup.mem_normalizer_iff.mp hs_norm uH).1 huH
  rcases (appendixCUInH_mem_iff (p := p) (q := q) _).1 hconj with ⟨v, hv⟩
  have hleft := congrArg SemidirectProduct.left hv
  have hleftAdd := congrArg Multiplicative.toAdd hleft
  have hu_field : ((u : (appendixCField p q)ˣ) : appendixCField p q) = 1 := by
    have hsub : (1 : appendixCField p q) -
        ((u : (appendixCField p q)ˣ) : appendixCField p q) = 0 := by
      simpa [s, uH, appendixCAction_apply_toAdd, sub_eq_add_neg] using hleftAdd
    exact (sub_eq_zero.mp hsub).symm
  apply hu
  ext
  exact hu_field

/-- Embedded form of the previous non-normalization fact, using a nontrivial
member of `E` to produce the nontrivial norm-one unit. -/
public theorem CFSG.appendixCEmbedding_CP0InH_not_normalizes_CUInH_of_mem_appendixCE_ne_one
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
    ¬ appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q))
      (Subgroup.map σ (appendixCUInH p q)) := by
  rcases appendixCE_exists_nontrivial_normOneUnit (p := p) (q := q) ha ha1 with
    ⟨u, hu⟩
  intro hnorm
  exact appendixCP0InH_not_normalizes_CUInH_of_nontrivial_normOneUnit
    (p := p) (q := q) hu
    (appendixCEmbedding_normalizes_reflect_of_injective (σ := σ) hσ hnorm)

/-- A nontrivial element of a subgroup of prime order generates it, so if that
element normalizes `P`, the whole subgroup normalizes `P`. -/
public theorem CFSG.appendixC_prime_order_subgroup_normalizes_of_nontrivial_mem
    {G : Type u} [Group G] {P1 P : Subgroup G}
    (hP1card : Nat.card P1 = p) {t : G} (ht : t ∈ P1) (htne : t ≠ 1)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) :
    appendixCNormalizes P1 P := by
  intro x hx
  let tg : P1 := ⟨t, ht⟩
  let xg : P1 := ⟨x, hx⟩
  have htgne : tg ≠ 1 := by
    intro h
    apply htne
    exact congrArg Subtype.val h
  have hxzp : xg ∈ Subgroup.zpowers tg :=
    mem_zpowers_of_prime_card (G := P1) hP1card htgne
  rcases Subgroup.mem_zpowers_iff.mp hxzp with ⟨n, hn⟩
  have hx_eq : x = t ^ n := by
    change (xg : G) = t ^ n
    simpa [tg, xg] using (congrArg Subtype.val hn).symm
  simpa [hx_eq] using
    (Subgroup.normalizer (P : Set G)).zpow_mem htP n

/-- Appendix C C.3 Step 3 endpoint: for nontrivial `t₁ ∈ P₁`, the intersection
`PU ∩ (PU)^{t₁}` is exactly `U`. -/
public theorem CFSG.appendixCEmbedding_H_inf_conjBy_eq_CUInH_of_mem_rightConjugate_ne_one
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] (hcop : Nat.Coprime p (Nat.card Q))
    {y t1 : G} (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hP1U : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCUInH p q)))
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1)
    (ht1 : t1 ∈ appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
    (ht1ne : t1 ≠ 1) :
    Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) ⊓
        (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))).conjBy t1 =
      Subgroup.map σ (appendixCUInH p q) := by
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let P1 : Subgroup G := appendixCRightConjugate P0img y
  let Pimg : Subgroup G := Subgroup.map σ (appendixCPInH p q)
  let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
  let Himg : Subgroup G := Subgroup.map σ (⊤ : Subgroup (appendixCH p q))
  by_contra hne
  have hUleX : Uimg ≤ Himg ⊓ Himg.conjBy t1 := by
    exact appendixCEmbedding_U_le_H_inf_conjBy_of_mem_rightConjugate
      (p := p) (q := q) σ (y := y) (t1 := t1) ht1 hP1U
  have ht1P : t1 ∈ Subgroup.normalizer (Pimg : Set G) := by
    exact appendixCEmbedding_CPInH_mem_normalizer_of_H_inf_conjBy_ne_U
      (p := p) (q := q) hA σ hσ (t := t1) ha ha1 hUleX
      (by simpa [Himg, Uimg] using hne)
  have hP0card : Nat.card P0img = p :=
    appendixCEmbedding_CP0InH_natCard (p := p) (q := q) σ hσ
  have hP1card : Nat.card P1 = p := by
    calc
      Nat.card P1 = Nat.card P0img := appendixCRightConjugate_natCard P0img y
      _ = p := hP0card
  have hP1P : appendixCNormalizes P1 Pimg := by
    exact appendixC_prime_order_subgroup_normalizes_of_nontrivial_mem
      (p := p) hP1card (show t1 ∈ P1 from by simpa [P1, P0img] using ht1)
      ht1ne ht1P
  have hP1eqP0 : P1 = P0img := by
    simpa [P1, P0img, Pimg] using
      appendixCEmbedding_rightConjugate_CP0InH_eq_CP0InH_of_normalizes_CPInH
        (p := p) (q := q) σ hσ Q hcop hy hP0Q hP1P
  have hP1U' : appendixCNormalizes P1 Uimg := by
    simpa [P1, P0img, Uimg] using hP1U
  have hP0U : appendixCNormalizes P0img Uimg := by
    simpa [hP1eqP0] using hP1U'
  exact appendixCEmbedding_CP0InH_not_normalizes_CUInH_of_mem_appendixCE_ne_one
    (p := p) (q := q) σ hσ ha ha1 hP0U

/-- If `t` is a nontrivial member of the prime-order right-conjugate `P₁`
and `p` is odd, then `t^2` is still nontrivial. This is the small order
calculation needed before applying Step 3 to the C9 intersection. -/
public theorem CFSG.appendixCEmbedding_rightConjugate_sq_ne_one_of_mem_ne_one
    {G : Type u} [Group G] (hoddp : Odd p)
    (σ : appendixCH p q →* G) (hσ : Function.Injective σ) {y t : G}
    (ht : t ∈ appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y)
    (htne : t ≠ 1) :
    t ^ 2 ≠ 1 := by
  have htpow : t ^ p = 1 :=
    appendixCEmbedding_rightConjugate_mem_pow_prime_eq_one
      (p := p) (q := q) σ hσ ht
  have horder : orderOf t = p := orderOf_eq_prime htpow htne
  intro ht2
  have hpdiv2 : p ∣ 2 := by
    rw [← horder]
    exact orderOf_dvd_iff_pow_eq_one.mpr ht2
  have hp_eq_two : p = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hpdiv2 with hp1 | hp2
    · exact False.elim ((Fact.out : Nat.Prime p).ne_one hp1)
    · exact hp2
  have hp_ne_two : p ≠ 2 := by
    intro hp
    rw [hp] at hoddp
    exact (by norm_num : ¬ Odd 2) hoddp
  exact hp_ne_two hp_eq_two

/-- If `s` is a nontrivial member of the embedded prime-field subgroup `P₀`
and `p` is odd, then `s^2` is nontrivial. -/
public theorem CFSG.appendixCEmbedding_CP0InH_sq_ne_one_of_mem_ne_one
    {G : Type u} [Group G] (hoddp : Odd p)
    (σ : appendixCH p q →* G) (hσ : Function.Injective σ) {s : G}
    (hs : s ∈ Subgroup.map σ (appendixCP0InH p q)) (hsne : s ≠ 1) :
    s ^ 2 ≠ 1 := by
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  have hs_right : s ∈ appendixCRightConjugate P0img (1 : G) :=
    (appendixCRightConjugate_mem_iff P0img (1 : G) s).2
      ⟨s, by simpa [P0img] using hs, by simp⟩
  exact appendixCEmbedding_rightConjugate_sq_ne_one_of_mem_ne_one
    (p := p) (q := q) hoddp σ hσ (y := (1 : G)) hs_right hsne

/-- Step 3 specialized to the square `t^2`, as used in the source after
equation C9. -/
public theorem CFSG.appendixCEmbedding_H_inf_conjBy_sq_eq_CUInH_of_mem_rightConjugate_ne_one
    {G : Type u} [Group G] [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p)
    (σ : appendixCH p q →* G) (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] (hcop : Nat.Coprime p (Nat.card Q))
    {y t : G} (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hP1U : appendixCNormalizes
      (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
      (Subgroup.map σ (appendixCUInH p q)))
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1)
    (ht : t ∈ appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
    (htne : t ≠ 1) :
    Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) ⊓
        (Subgroup.map σ (⊤ : Subgroup (appendixCH p q))).conjBy (t ^ 2) =
      Subgroup.map σ (appendixCUInH p q) := by
  exact appendixCEmbedding_H_inf_conjBy_eq_CUInH_of_mem_rightConjugate_ne_one
    (p := p) (q := q) hA σ hσ Q hcop hy hP0Q hP1U ha ha1
    ((appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y).pow_mem ht 2)
    (appendixCEmbedding_rightConjugate_sq_ne_one_of_mem_ne_one
      (p := p) (q := q) hoddp σ hσ ht htne)

/-- Core of Lemma C.1 after choosing `a ∈ E \ {1}`. The source proves this by
iterating `τ(a) = (2 - a)⁻¹`, obtaining norm-one values for every element of
`F_p`, and applying the root bound to a degree-`q` norm polynomial. -/
public theorem CFSG.appendixC_lemma_C_1_core
    [Fact q.Prime]
    (hE : appendixCInversionStable p q (appendixCE p q))
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
    p ≤ q := by
  have hdeg : (appendixCNormPoly p q a).natDegree = q :=
    appendixCNormPoly_natDegree (p := p) (q := q) ha1
  have hnonzero : appendixCNormPoly p q a ≠ 0 := by
    intro hzero
    have hqprime : Nat.Prime q := Fact.out
    rw [hzero, Polynomial.natDegree_zero] at hdeg
    exact hqprime.ne_zero (by omega)
  have hle :
      p ≤ (appendixCNormPoly p q a).natDegree :=
    zmod_card_le_natDegree_of_eval_algebraMap_eq_zero
      (p := p) (F := appendixCField p q) (appendixCNormPoly p q a) hnonzero
      (appendixCNormPoly_eval_algebraMap_eq_zero (p := p) (q := q) hE ha)
  simpa [hdeg] using hle

/-- Lemma C.1. If `E = E^{-1}` and `|E| ≥ 2`, then `p ≤ q`. -/
public theorem CFSG.appendixC_lemma_C_1
    [Fact q.Prime]
    (hE : appendixCInversionStable p q (appendixCE p q))
    (hcard : 2 ≤ Nat.card (appendixCE p q)) :
    p ≤ q := by
  rcases appendixCE_exists_ne_one_of_two_le_card (p := p) (q := q) hcard with
    ⟨a, ha, ha1⟩
  exact appendixC_lemma_C_1_core (p := p) (q := q) hE ha ha1


end

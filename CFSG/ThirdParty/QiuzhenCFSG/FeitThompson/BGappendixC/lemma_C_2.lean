module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGappendixC.lemma_C_1

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped Pointwise

noncomputable section

universe u v

variable (p q : ℕ) [Fact p.Prime]

/-- The cubic `f_c(X) = X(X-2)(X-c)+(X-1)` used in the `q = 3`
branch of Appendix C Lemma C.2. -/
public def CFSG.appendixCCubic (p : ℕ) (c : ZMod p) : Polynomial (ZMod p) :=
  Polynomial.X * (Polynomial.X - Polynomial.C 2) * (Polynomial.X - Polynomial.C c) +
    (Polynomial.X - Polynomial.C 1)

/-- The source cubic is nonzero at `0`. -/
public theorem CFSG.appendixCCubic_eval_zero_ne_zero
    (c : ZMod p) :
    (appendixCCubic p c).eval 0 ≠ 0 := by
  have h : (appendixCCubic p c).eval 0 = -1 := by
    simp [appendixCCubic]
  rw [h]
  exact neg_ne_zero.mpr one_ne_zero

/-- The source cubic is nonzero at `2`. -/
public theorem CFSG.appendixCCubic_eval_two_ne_zero
    (c : ZMod p) :
    (appendixCCubic p c).eval 2 ≠ 0 := by
  have h : (appendixCCubic p c).eval 2 = 1 := by
    simp [appendixCCubic]
    ring
  rw [h]
  exact one_ne_zero

/-- In a prime field of odd characteristic, `0` and `2` are distinct. -/
public theorem CFSG.zmod_zero_ne_two_of_prime_ne_two
    (hp2 : p ≠ 2) :
    (0 : ZMod p) ≠ 2 := by
  intro h
  have hdvd : p ∣ 2 := by
    rw [← CharP.cast_eq_zero_iff (ZMod p) p 2]
    simpa using h.symm
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with hp1 | hp2'
  · exact (Fact.out : Nat.Prime p).ne_one hp1
  · exact hp2 hp2'

/-- The prime field with `0` and `2` removed has cardinality `p - 2`
when `p ≠ 2`. -/
public theorem CFSG.natCard_zmod_ne_zero_ne_two
    (hp2 : p ≠ 2) :
    Nat.card {x : ZMod p // x ≠ 0 ∧ x ≠ 2} = p - 2 := by
  have h02 : (0 : ZMod p) ≠ 2 :=
    zmod_zero_ne_two_of_prime_ne_two (p := p) hp2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter (fun x : ZMod p => x ≠ 0 ∧ x ≠ 2)) =
        (Finset.univ.erase (0 : ZMod p)).erase (2 : ZMod p) := by
    ext x
    by_cases hx0 : x = 0 <;> by_cases hx2 : x = 2 <;>
      simp [hx0, hx2, eq_comm]
  rw [hfilter]
  rw [Finset.card_erase_of_mem]
  · rw [Finset.card_erase_of_mem]
    · rw [Finset.card_univ, ZMod.card]
      omega
    · simp
  · simp [h02.symm]

/-- Two source cubics with the same root away from `0` and `2` have the same
parameter. -/
public theorem CFSG.appendixCCubic_same_root_eq
    {a b d : ZMod p} (hd0 : d ≠ 0) (hd2 : d ≠ 2)
    (ha : (appendixCCubic p a).eval d = 0)
    (hb : (appendixCCubic p b).eval d = 0) :
    a = b := by
  have hsum : d * (d - 2) * (d - a) + (d - 1) =
      d * (d - 2) * (d - b) + (d - 1) := by
    simpa [appendixCCubic] using ha.trans hb.symm
  have hprod : d * (d - 2) * (d - a) = d * (d - 2) * (d - b) :=
    add_right_cancel hsum
  have hfactor : d * (d - 2) ≠ 0 :=
    mul_ne_zero hd0 ((sub_ne_zero).2 hd2)
  have hsub : d - a = d - b := mul_left_cancel₀ hfactor hprod
  exact (sub_right_inj).1 hsub

/-- In odd prime characteristic, one of the source cubics has no root in the
prime field. This is the pigeonhole step in the `q = 3` branch of Lemma C.2. -/
public theorem CFSG.exists_appendixCCubic_without_zmod_root
    (hp2 : p ≠ 2) :
    ∃ c : ZMod p, ∀ x : ZMod p, (appendixCCubic p c).eval x ≠ 0 := by
  by_contra hnot
  push Not at hnot
  let root : ZMod p → ZMod p := fun c => Classical.choose (hnot c)
  have hroot : ∀ c, (appendixCCubic p c).eval (root c) = 0 := by
    intro c
    exact Classical.choose_spec (hnot c)
  let f : ZMod p → {x : ZMod p // x ≠ 0 ∧ x ≠ 2} := fun c =>
    ⟨root c, by
      constructor
      · intro h0
        have hzero := hroot c
        rw [h0] at hzero
        exact appendixCCubic_eval_zero_ne_zero (p := p) c hzero
      · intro h2
        have hzero := hroot c
        rw [h2] at hzero
        exact appendixCCubic_eval_two_ne_zero (p := p) c hzero⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hroot_eq : root a = root b := Subtype.ext_iff.mp hab
    exact appendixCCubic_same_root_eq (p := p)
      (a := a) (b := b) (d := root a)
      (show root a ≠ 0 from (f a).property.1)
      (show root a ≠ 2 from (f a).property.2)
      (hroot a)
      (by simpa [hroot_eq] using hroot b)
  have hle := Nat.card_le_card_of_injective f hf
  have hcard : Nat.card {x : ZMod p // x ≠ 0 ∧ x ≠ 2} = p - 2 :=
    natCard_zmod_ne_zero_ne_two (p := p) hp2
  have hzmod : Nat.card (ZMod p) = p := by simp
  rw [hzmod, hcard] at hle
  have hlt : p - 2 < p := Nat.sub_lt (Fact.out : Nat.Prime p).pos (by norm_num)
  exact not_lt_of_ge hle hlt

/-- The source cubic is monic. -/
public theorem CFSG.appendixCCubic_monic
    (c : ZMod p) :
    (appendixCCubic p c).Monic := by
  unfold appendixCCubic
  monicity!

/-- The cubic part of the source cubic has degree three. -/
public theorem CFSG.appendixCCubic_prod_natDegree
    (c : ZMod p) :
    (Polynomial.X * (Polynomial.X - Polynomial.C 2) *
        (Polynomial.X - Polynomial.C c) : Polynomial (ZMod p)).natDegree = 3 := by
  rw [Polynomial.natDegree_mul, Polynomial.natDegree_mul]
  · simp [Polynomial.natDegree_X]
  · exact Polynomial.X_ne_zero
  · exact (Polynomial.monic_X_sub_C (2 : ZMod p)).ne_zero
  · exact mul_ne_zero Polynomial.X_ne_zero
      (Polynomial.monic_X_sub_C (2 : ZMod p)).ne_zero
  · exact (Polynomial.monic_X_sub_C c).ne_zero

/-- The source cubic has degree three. -/
public theorem CFSG.appendixCCubic_natDegree
    (c : ZMod p) :
    (appendixCCubic p c).natDegree = 3 := by
  unfold appendixCCubic
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact appendixCCubic_prod_natDegree (p := p) c
  · rw [appendixCCubic_prod_natDegree (p := p) c, Polynomial.natDegree_X_sub_C]
    norm_num

/-- A rootless source cubic over the prime field is irreducible. -/
public theorem CFSG.appendixCCubic_irreducible_of_no_zmod_root
    {c : ZMod p} (hrootless : ∀ x : ZMod p, (appendixCCubic p c).eval x ≠ 0) :
    Irreducible (appendixCCubic p c) := by
  have hf0 : appendixCCubic p c ≠ 0 := (appendixCCubic_monic (p := p) c).ne_zero
  have hroots : (appendixCCubic p c).roots = 0 := by
    rw [Polynomial.roots_eq_zero_iff_isRoot_eq_bot hf0]
    ext x
    simp [Polynomial.IsRoot.def, hrootless x]
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · exact hroots
  · rw [appendixCCubic_natDegree (p := p) c]
    norm_num
  · rw [appendixCCubic_natDegree (p := p) c]

/-- In the adjoined-root algebra, the source cubic root has norm one. -/
public theorem CFSG.appendixCCubic_adjoinRoot_norm_root_eq_one
    (c : ZMod p) :
    Algebra.norm (ZMod p) (AdjoinRoot.root (appendixCCubic p c)) = 1 := by
  let f := appendixCCubic p c
  have hfmonic : f.Monic := by
    simpa [f] using appendixCCubic_monic (p := p) c
  have hf0 : f ≠ 0 := hfmonic.ne_zero
  have hnorm :=
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (AdjoinRoot.powerBasis hf0)
  rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim, AdjoinRoot.minpoly_root hf0]
    at hnorm
  have hlead : f.leadingCoeff = 1 := hfmonic.leadingCoeff
  have hcoeff : (f * Polynomial.C f.leadingCoeff⁻¹).coeff 0 = -1 := by
    rw [hlead]
    simp [f, appendixCCubic]
  rw [hcoeff] at hnorm
  rw [show f.natDegree = 3 by
    simpa [f] using appendixCCubic_natDegree (p := p) c] at hnorm
  norm_num at hnorm
  simpa [f] using hnorm

/-- In the adjoined-root algebra, the element `2 - root` also has norm one.
This is the determinant computation behind the `q = 3` branch of Lemma C.2:
`f_c(2) = 1`. -/
public theorem CFSG.appendixCCubic_adjoinRoot_norm_two_sub_root_eq_one
    (c : ZMod p) :
    Algebra.norm (ZMod p)
      (algebraMap (ZMod p) (AdjoinRoot (appendixCCubic p c)) (2 : ZMod p) -
        AdjoinRoot.root (appendixCCubic p c)) = 1 := by
  let f := appendixCCubic p c
  have hfmonic : f.Monic := by
    simpa [f] using appendixCCubic_monic (p := p) c
  have hf0 : f ≠ 0 := hfmonic.ne_zero
  let pb := AdjoinRoot.powerBasis hf0
  have hdim : pb.dim = 3 := by
    simpa [pb, f] using appendixCCubic_natDegree (p := p) c
  have hminpoly : minpoly (ZMod p) pb.gen = f := by
    simpa [pb] using AdjoinRoot.minpoly_powerBasis_gen_of_monic hfmonic hf0
  have hcoeff0 : (minpoly (ZMod p) pb.gen).coeff 0 = -1 := by
    rw [hminpoly]
    simp [f, appendixCCubic]
  have hcoeff1 : (minpoly (ZMod p) pb.gen).coeff 1 = 2 * c + 1 := by
    rw [hminpoly]
    simp [f, appendixCCubic, Finset.Nat.antidiagonal_succ, Polynomial.coeff_one,
      Polynomial.coeff_X, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul]
  have hcoeff2 : 2 + (minpoly (ZMod p) pb.gen).coeff 2 = -c := by
    rw [hminpoly]
    simp [f, appendixCCubic, Finset.Nat.antidiagonal_succ, Polynomial.coeff_one,
      Polynomial.coeff_X, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul]
  have hscalar :
      Algebra.leftMulMatrix pb.basis
        (algebraMap (ZMod p) (AdjoinRoot f) (2 : ZMod p)) =
        algebraMap (ZMod p) (Matrix (Fin pb.dim) (Fin pb.dim) (ZMod p))
          (2 : ZMod p) := by
    exact AlgHom.commutes (Algebra.leftMulMatrix pb.basis) (2 : ZMod p)
  rw [Algebra.norm_eq_matrix_det pb.basis]
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  rw [← Matrix.det_reindex_self e
    (Algebra.leftMulMatrix pb.basis
      (algebraMap (ZMod p) (AdjoinRoot f) (2 : ZMod p) - AdjoinRoot.root f))]
  rw [map_sub]
  change ((Matrix.reindex e e)
        ((Algebra.leftMulMatrix pb.basis) ((algebraMap (ZMod p) (AdjoinRoot f)) 2) -
          (Algebra.leftMulMatrix pb.basis) pb.gen)).det = 1
  rw [PowerBasis.leftMulMatrix]
  have hmat :
      Matrix.reindex e e
        (Algebra.leftMulMatrix pb.basis
            (algebraMap (ZMod p) (AdjoinRoot f) (2 : ZMod p)) -
          @Matrix.of (Fin pb.dim) (Fin pb.dim) (ZMod p)
            (fun i j =>
              if ↑j + 1 = pb.dim then -pb.minpolyGen.coeff ↑i
              else if (i : ℕ) = j + 1 then 1 else 0)) =
        !![(2 : ZMod p), 0, -1;
           -1, 2, 2 * c + 1;
           0, -1, -c] := by
    rw [hscalar]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, hdim, Matrix.algebraMap_matrix_apply, hcoeff0, hcoeff1, hcoeff2]
  rw [hmat, Matrix.det_fin_three]
  simp
  ring_nf


/-- A rootless source cubic has a root in `F_{p^3}` lying in the Appendix C
set `E`: both `a` and `2 - a` have norm one. -/
public theorem CFSG.appendixCCubic_exists_root_mem_appendixCE_in_q3
    {c : ZMod p} (hrootless : ∀ x : ZMod p, (appendixCCubic p c).eval x ≠ 0) :
    ∃ a : appendixCField p 3,
      ((appendixCCubic p c).map
        (algebraMap (ZMod p) (appendixCField p 3))).eval a = 0 ∧
      a ∈ appendixCE p 3 := by
  let f := appendixCCubic p c
  have hfmonic : f.Monic := by
    simpa [f] using appendixCCubic_monic (p := p) c
  have hirr : Irreducible f := by
    simpa [f] using appendixCCubic_irreducible_of_no_zmod_root (p := p) hrootless
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  haveI : Module.Finite (ZMod p) (AdjoinRoot f) := hfmonic.finite_adjoinRoot
  have hfinrank_adjoin : Module.finrank (ZMod p) (AdjoinRoot f) = 3 := by
    change Module.finrank (ZMod p) (Polynomial (ZMod p) ⧸ Ideal.span {f}) = 3
    rw [finrank_quotient_span_eq_natDegree]
    simpa [f] using appendixCCubic_natDegree (p := p) c
  have hfinrank_field : Module.finrank (ZMod p) (appendixCField p 3) = 3 :=
    GaloisField.finrank p (n := 3) (by norm_num)
  have hnonempty : Nonempty (AdjoinRoot f →ₐ[ZMod p] appendixCField p 3) := by
    apply FiniteField.nonempty_algHom_of_finrank_dvd
    rw [hfinrank_adjoin, hfinrank_field]
  rcases hnonempty with ⟨φ⟩
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot f) := Fintype.ofFinite (AdjoinRoot f)
  haveI : Fintype (appendixCField p 3) := Fintype.ofFinite (appendixCField p 3)
  have hcardNat : Nat.card (AdjoinRoot f) = p ^ 3 := by
    rw [@Module.natCard_eq_pow_finrank (ZMod p) (AdjoinRoot f)]
    rw [hfinrank_adjoin, Nat.card_zmod]
  have hcard : Fintype.card (AdjoinRoot f) = Fintype.card (appendixCField p 3) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    rw [hcardNat, GaloisField.card p (n := 3) (by norm_num)]
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨RingHom.injective φ.toRingHom, hcard⟩
  let e : AdjoinRoot f ≃ₐ[ZMod p] appendixCField p 3 := AlgEquiv.ofBijective φ hbij
  refine ⟨e (AdjoinRoot.root f), ?_, ?_, ?_⟩
  · have hroot := AdjoinRoot.aeval_algHom_eq_zero f e.toAlgHom
    simpa [Polynomial.aeval_def, Polynomial.eval_map, f] using hroot
  · rw [Algebra.norm_eq_of_algEquiv e (AdjoinRoot.root f)]
    simpa [f] using appendixCCubic_adjoinRoot_norm_root_eq_one (p := p) c
  · change Algebra.norm (ZMod p)
        (algebraMap (ZMod p) (appendixCField p 3) (2 : ZMod p) -
          e (AdjoinRoot.root f)) = 1
    rw [← show
        e (algebraMap (ZMod p) (AdjoinRoot f) (2 : ZMod p) - AdjoinRoot.root f) =
          algebraMap (ZMod p) (appendixCField p 3) (2 : ZMod p) -
            e (AdjoinRoot.root f) by
          rw [map_sub]
          congr 1
          exact e.commutes (2 : ZMod p)]
    rw [Algebra.norm_eq_of_algEquiv e
      (algebraMap (ZMod p) (AdjoinRoot f) (2 : ZMod p) - AdjoinRoot.root f)]
    simpa [f] using
      appendixCCubic_adjoinRoot_norm_two_sub_root_eq_one (p := p) c


/-- The root in `F_{p^3}` produced from a rootless source cubic is not `1`,
because otherwise the source cubic would have the prime-field root `1`. -/
public theorem CFSG.appendixCCubic_root_ne_one_of_no_zmod_root
    {c : ZMod p} {a : appendixCField p 3}
    (hrootless : ∀ x : ZMod p, (appendixCCubic p c).eval x ≠ 0)
    (ha : ((appendixCCubic p c).map
      (algebraMap (ZMod p) (appendixCField p 3))).eval a = 0) :
    a ≠ 1 := by
  intro ha1
  have hroot_one : (appendixCCubic p c).eval (1 : ZMod p) = 0 := by
    apply FaithfulSMul.algebraMap_injective (ZMod p) (appendixCField p 3)
    simpa [Polynomial.eval_map, ha1] using ha
  exact hrootless 1 hroot_one

/-- The `q = 3` branch of Lemma C.2. The cubic construction produces a
non-one element of `E`, hence `|E| ≥ 2`. -/
public theorem CFSG.appendixC_lemma_C_2_of_q_eq_three
    [Fact q.Prime]
    (hoddp : Odd p) (hq3 : q = 3) :
    2 ≤ Nat.card (appendixCE p q) := by
  subst q
  have hp2 : p ≠ 2 := by
    rcases hoddp with ⟨k, hk⟩
    omega
  rcases exists_appendixCCubic_without_zmod_root (p := p) hp2 with ⟨c, hrootless⟩
  rcases appendixCCubic_exists_root_mem_appendixCE_in_q3 (p := p) hrootless with
    ⟨a, hroot, haE⟩
  exact two_le_card_appendixCE_of_mem_ne_one (p := p) (q := 3) haE
    (appendixCCubic_root_ne_one_of_no_zmod_root (p := p) hrootless hroot)

/-- An odd prime different from `3` is at least `5`. This is the arithmetic
split used in the non-cubic branch of Lemma C.2. -/
public theorem CFSG.appendixC_prime_odd_ne_three_five_le
    [Fact q.Prime] (hoddq : Odd q) (hq3 : q ≠ 3) :
    5 ≤ q := by
  have hq : Nat.Prime q := Fact.out
  have hq2le : 2 ≤ q := hq.two_le
  rcases hoddq with ⟨k, hk⟩
  by_contra hnot
  have hlt5 : q < 5 := Nat.lt_of_not_ge hnot
  have hq3' : q = 3 := by omega
  exact hq3 hq3'


/-- The remaining character-counting estimate in the `q ≥ 5` branch of
Lemma C.2. This uses the norm-character count formula: the trivial-trivial
term is `p^q - 2`, while the remaining character pairs are bounded by the
Jacobi-sum estimates above. -/
public theorem CFSG.appendixC_lemma_C_2_character_count_bound
    [Fact q.Prime]
    (_hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hq5 : 5 ≤ q) :
    2 ≤ Nat.card (appendixCE p q) := by
  classical
  by_contra hnot
  have hE_le_one : Nat.card (appendixCE p q) ≤ 1 := by
    omega
  letI : Fintype (appendixCField p q) := Fintype.ofFinite _
  letI : Fintype (appendixCE p q) := Fintype.ofFinite _
  let X := (ZMod p)ˣ →* ℂˣ
  letI : Fintype X := Fintype.ofFinite _
  letI : DecidableEq X := Classical.decEq X
  have hexp : Monoid.ExponentExists (ZMod p)ˣ := Monoid.ExponentExists.of_finite
  haveI : NeZero (Monoid.exponent (ZMod p)ˣ) :=
    ⟨(Monoid.exponent_ne_zero.2 hexp)⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod p)ˣ) :=
    appendixC_complex_hasEnoughRootsOfUnity (Monoid.exponent (ZMod p)ˣ)
  let pairOne : X × X := ((1 : X), 1)
  let pairs : Finset (X × X) := (Finset.univ : Finset (X × X)).erase pairOne
  let term : X × X → ℂ := fun x =>
    ∑ z : appendixCField p q,
      appendixCNormCharacter p q x.1 z *
        appendixCNormCharacter p q x.2 ((2 : appendixCField p q) - z)
  let R : ℂ := pairs.sum term
  let smallNat : ℕ := (p - 1) * (p - 1)
  let bigNat : ℕ := (p - 2) * (p - 3) * p ^ (q / 2 + 1)
  let unitNat : ℕ := Nat.card (ZMod p)ˣ
  let totalNat : ℕ := unitNat * unitNat * Nat.card (appendixCE p q)
  let mainNat : ℕ := p ^ q - 2
  have hp : Nat.Prime p := Fact.out
  have hq : Nat.Prime q := Fact.out
  have hpq_two : 2 ≤ p ^ q := by
    calc
      2 ≤ p := hp.two_le
      _ = p ^ 1 := by rw [pow_one]
      _ ≤ p ^ q := Nat.pow_le_pow_right hp.pos hq.pos
  have hformula :
      (∑ χ : X, ∑ ψ : X, term (χ, ψ)) =
        (totalNat : ℂ) := by
    simpa [X, term, totalNat, unitNat, Nat.cast_mul] using
      appendixCE_character_sum_formula (p := p) (q := q)
  have hprod :
      (∑ χ : X, ∑ ψ : X, term (χ, ψ)) =
        (Finset.univ : Finset (X × X)).sum term := by
    rw [← Finset.sum_product]
    simp
  have hsplit :
      (Finset.univ : Finset (X × X)).sum term = term pairOne + R := by
    have hmem : pairOne ∈ (Finset.univ : Finset (X × X)) := by simp
    have h := Finset.sum_erase_add
      (s := (Finset.univ : Finset (X × X))) (f := term) hmem
    change pairs.sum term + term pairOne =
      (Finset.univ : Finset (X × X)).sum term at h
    rw [← h]
    abel
  have htriv : term pairOne = (mainNat : ℂ) := by
    have hcast : (p ^ q : ℂ) - 2 = (mainNat : ℂ) := by
      simpa [mainNat] using (Nat.cast_sub (R := ℂ) hpq_two).symm
    rw [← hcast]
    simpa [term, pairOne] using
      appendixC_norm_character_trivial_trivial_sum (p := p) (q := q) hoddp
  have hcomplex : (mainNat : ℂ) + R = (totalNat : ℂ) := by
    calc
      (mainNat : ℂ) + R = term pairOne + R := by rw [htriv]
      _ = (Finset.univ : Finset (X × X)).sum term := hsplit.symm
      _ = ∑ χ : X, ∑ ψ : X, term (χ, ψ) := hprod.symm
      _ = (totalNat : ℂ) := hformula
  have hmain_eq : (mainNat : ℂ) = (totalNat : ℂ) - R := by
    rw [← hcomplex]
    abel
  have hmain_le : (mainNat : ℝ) ≤ (totalNat : ℝ) + ‖R‖ := by
    calc
      (mainNat : ℝ) = ‖(mainNat : ℂ)‖ := by simp
      _ = ‖(totalNat : ℂ) - R‖ := by rw [hmain_eq]
      _ ≤ ‖(totalNat : ℂ)‖ + ‖R‖ := norm_sub_le _ _
      _ = (totalNat : ℝ) + ‖R‖ := by simp
  have hrem0 := appendixC_character_sum_remainder_norm_bound (p := p) (q := q) hoddp
  have hrem : ‖R‖ ≤ (smallNat : ℝ) + (bigNat : ℝ) := by
    simpa [R, pairs, term, pairOne, smallNat, bigNat, Nat.cast_mul,
      mul_assoc] using hrem0
  have htotal_le : totalNat ≤ smallNat := by
    have hUnitcard : unitNat = p - 1 := by
      dsimp [unitNat]
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card_units p
    dsimp [totalNat, smallNat]
    rw [hUnitcard]
    calc
      (p - 1) * (p - 1) * Nat.card (appendixCE p q) ≤
          (p - 1) * (p - 1) * 1 :=
        Nat.mul_le_mul_left ((p - 1) * (p - 1)) hE_le_one
      _ = (p - 1) * (p - 1) := by simp
  have htotal_real : (totalNat : ℝ) ≤ (smallNat : ℝ) := by
    exact_mod_cast htotal_le
  have hmain_upper :
      (mainNat : ℝ) ≤ (smallNat : ℝ) + ((smallNat : ℝ) + (bigNat : ℝ)) := by
    linarith
  have hmain_add : mainNat + 2 = p ^ q := by
    simpa [mainNat] using Nat.sub_add_cancel hpq_two
  have hupper_nat :
      (p ^ q : ℝ) ≤ ((smallNat + smallNat + bigNat + 2 : ℕ) : ℝ) := by
    have hcast_main : (mainNat : ℝ) + 2 = (p ^ q : ℝ) := by
      exact_mod_cast hmain_add
    have hcast_upper :
        (smallNat : ℝ) + ((smallNat : ℝ) + (bigNat : ℝ)) + 2 =
          (smallNat + smallNat + bigNat + 2 : ℕ) := by
      norm_num [Nat.cast_add]
      ring
    linarith
  have harith :=
    appendixC_lemma_C_2_coarse_count_arithmetic
      (p := p) (q := q) hoddp hoddq hq5
  have harith_real :
      ((smallNat + smallNat + bigNat + 2 : ℕ) : ℝ) < (p ^ q : ℝ) := by
    have hsmall_eq : smallNat + smallNat + bigNat + 2 =
        2 * ((p - 1) * (p - 1)) + 2 +
          (p - 2) * (p - 3) * p ^ (q / 2 + 1) := by
      simp [smallNat, bigNat]
      ring
    rw [hsmall_eq]
    exact_mod_cast harith
  linarith

/-- The remaining non-`q = 3` branch of Lemma C.2. The source proof uses the
character-counting argument for odd primes `q ≥ 5`. -/
public theorem CFSG.appendixC_lemma_C_2_of_q_ne_three
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hq3 : q ≠ 3) :
    2 ≤ Nat.card (appendixCE p q) := by
  have hq5 : 5 ≤ q :=
    appendixC_prime_odd_ne_three_five_le (q := q) hoddq hq3
  exact appendixC_lemma_C_2_character_count_bound (p := p) (q := q)
    hA hoddp hoddq hq5

/-- Lemma C.2. Under condition `(A)` for odd primes, `|E| ≥ 2`. -/
public theorem CFSG.appendixC_lemma_C_2
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q) :
    2 ≤ Nat.card (appendixCE p q) := by
  by_cases hq3 : q = 3
  · exact appendixC_lemma_C_2_of_q_eq_three (p := p) (q := q) hoddp hq3
  · exact appendixC_lemma_C_2_of_q_ne_three (p := p) (q := q)
      hA hoddp hoddq hq3


end

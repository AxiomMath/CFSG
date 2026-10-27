module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZBlockO2
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoUnitary
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open CFSG.StandardType.ClassicalBlocks CFSG.StandardType.ClassicalPosition Matrix

private lemma l937z_su_exists_pow_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (q : ℕ) (hq2 : 2 ≤ q) (hK : Nat.card K = q ^ 2) : ∃ j : ℕ, j ≠ 0 ∧ q = 2 ^ j := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hK' : q ^ 2 = 2 ^ (m : ℕ) := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact hm
  have hdvd : q ∣ 2 ^ (m : ℕ) := by rw [← hK']; exact dvd_pow_self q (by norm_num)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨j, ?_, hj⟩
  rintro rfl
  simp at hj
  omega

private lemma l937z_su_exists_mu {K : Type} [Field K] [Finite K] (q : ℕ)
    (hq2 : 2 ≤ q) (hK : Nat.card K = q ^ 2) : ∃ μ : Kˣ, orderOf μ = q + 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : IsCyclic Kˣ := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by rw [Nat.card_units, hK]
  have hdvd : q - 1 ∣ q ^ 2 - 1 := by
    have h : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h1 : 1 ≤ q := by omega
      nlinarith [Nat.sub_add_cancel h1, Nat.sq_sub_sq q 1]
    exact ⟨q + 1, by rw [h, mul_comm]⟩
  have hgcd : (q ^ 2 - 1).gcd (q - 1) = q - 1 := Nat.gcd_eq_right hdvd
  have hpos : 0 < q - 1 := by omega
  refine ⟨g ^ (q - 1), ?_⟩
  rw [orderOf_pow, hg, hcard, hgcd]
  have h : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q := by omega
    nlinarith [Nat.sub_add_cancel h1, Nat.sq_sub_sq q 1]
  rw [h, Nat.mul_div_cancel_left _ hpos]

private lemma l937z_sua_frob_pow {K : Type} [Field K] (σ : K ≃+* K)
    (hσ : ∀ a, σ a = a ^ 2) (j : ℕ) (x : K) : (σ ^ j) x = x ^ 2 ^ j := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, RingAut.mul_apply, ih (σ x), hσ, ← pow_mul, pow_succ, mul_comm]

private lemma l937z_su_subfield {K : Type} [Field K] [Finite K] [CharP K 2] (q : ℕ)
    (hq2 : 2 ≤ q) (hK : Nat.card K = q ^ 2) :
    ∃ k : Subfield K, Nat.card ↥k = q ∧ ∀ x : K, x ∈ k ↔ x ^ q = x := by
  obtain ⟨j, hj0, hq⟩ := l937z_su_exists_pow_two q hq2 hK
  subst q
  have hF : Nat.card K = 2 ^ (2 * j) := by
    rw [hK, ← pow_mul, Nat.mul_comm j 2]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ, hσord, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * j) hF
  obtain ⟨-, S, hS, hScard⟩ := hA (Subgroup.zpowers (σ ^ j))
  have hcardA : Nat.card ↥(Subgroup.zpowers (σ ^ j)) = 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime
    · rw [← pow_mul, mul_comm j 2, ← hσord]
      exact pow_orderOf_eq_one σ
    · intro h
      have hdvd : orderOf σ ∣ j := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hσord] at hdvd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hdvd
      omega
  rw [hcardA, Nat.mul_div_cancel_left j (by norm_num : 0 < 2)] at hScard
  refine ⟨S, hScard, ?_⟩
  have hmem : ∀ x : K, x ∈ S ↔ (σ ^ j) x = x := by
    intro x
    change x ∈ (S : Set K) ↔ (σ ^ j) x = x
    rw [hS]
    constructor
    · intro h; exact h _ (Subgroup.mem_zpowers _)
    · intro h τ hτ
      have hle : Subgroup.zpowers (σ ^ j) ≤ MulAction.stabilizer (K ≃+* K) x :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (by simpa using h))
      exact MulAction.mem_stabilizer_iff.mp (hle hτ)
  intro x
  rw [hmem x, l937z_sua_frob_pow σ hσ j x]

private lemma l937z_su_mu_data {K : Type} [Field K] [Finite K] [CharP K 2] (q : ℕ)
    (hq2 : 2 ≤ q) (hK : Nat.card K = q ^ 2) (k : Subfield K) (hk : ∀ x : K, x ∈ k ↔ x ^ q = x) :
    ∃ (μ : K) (a : ↥k), orderOf μ = q + 1 ∧ (a : K) = μ + μ ^ q ∧
      μ ^ 2 + (a : K) * μ + 1 = 0 ∧
      Irreducible (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 : Polynomial ↥k) := by
  obtain ⟨j, -, hq⟩ := l937z_su_exists_pow_two q hq2 hK
  obtain ⟨u, hu⟩ := l937z_su_exists_mu q hq2 hK
  let μ : K := (u : K)
  have hμord : orderOf μ = q + 1 := by
    change orderOf (u : K) = q + 1
    rw [orderOf_units, hu]
  have hμ1 : μ ^ (q + 1) = 1 := by rw [← hμord]; exact pow_orderOf_eq_one μ
  have hμmul : μ * μ ^ q = 1 := by rw [← pow_succ', hμ1]
  have hμqsq : μ ^ (q ^ 2) = μ := by
    have hq2' : q ^ 2 = (q + 1) * (q - 1) + 1 := by
      have h1 : 1 ≤ q := by omega
      nlinarith [Nat.sub_add_cancel h1, Nat.sq_sub_sq q 1]
    calc μ ^ (q ^ 2) = μ ^ ((q + 1) * (q - 1) + 1) := by rw [hq2']
      _ = μ ^ ((q + 1) * (q - 1)) * μ ^ 1 := by rw [pow_add]
      _ = (μ ^ (q + 1)) ^ (q - 1) * μ := by rw [pow_mul, pow_one]
      _ = 1 ^ (q - 1) * μ := by rw [hμ1]
      _ = μ := by rw [one_pow, one_mul]
  have hμqmem : μ + μ ^ q ∈ k := by
    rw [hk]
    have hadd : (μ + μ ^ q) ^ q = μ ^ q + (μ ^ q) ^ q := by
      rw [hq]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact add_pow_char_pow (R := K) (p := 2) (n := j) μ (μ ^ 2 ^ j)
    rw [hadd, ← pow_mul, ← sq, hμqsq, add_comm]
  let a : ↥k := ⟨μ + μ ^ q, hμqmem⟩
  refine ⟨μ, a, hμord, rfl, ?_, ?_⟩
  · change μ ^ 2 + (μ + μ ^ q) * μ + 1 = 0
    have h1 : (μ + μ ^ q) * μ = μ ^ 2 + μ ^ (q + 1) := by
      rw [add_mul, ← pow_succ]
      ring
    rw [h1, hμ1, CharTwo.add_cancel_left, CharTwo.add_self_eq_zero]
  · let P : Polynomial ↥k := Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1
    show Irreducible P
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · have hdeg : P.natDegree = 2 := by
        have h := Polynomial.natDegree_quadratic (a := (1 : ↥k)) (b := a) (c := 1)
          (by norm_num)
        simpa [P, Polynomial.C_1, one_mul] using h
      rw [hdeg]
      decide
    · intro x hx
      rw [Polynomial.IsRoot.def] at hx
      have hx' : x ^ 2 + a * x + 1 = 0 := by
        simpa [P] using hx
      have hxK : (x : K) ^ 2 + (a : K) * (x : K) + 1 = 0 := by
        have hc := congrArg (Subfield.subtype k) hx'
        simpa [Subfield.coe_subtype] using hc
      have hprod : ((x : K) + μ) * ((x : K) + μ ^ q) = 0 := by
        have h1 : ((x : K) + μ) * ((x : K) + μ ^ q) =
            (x : K) ^ 2 + (a : K) * (x : K) + 1 := by
          rw [show (a : K) = μ + μ ^ q from rfl, ← hμmul]
          ring
        rw [h1, hxK]
      have hmuq : μ ^ q = μ := by
        rcases mul_eq_zero.mp hprod with h | h
        · have hxμ : (x : K) = μ := CharTwo.add_eq_zero.mp h
          exact (hk μ).mp (by rw [← hxμ]; exact x.2)
        · have hxμ : (x : K) = μ ^ q := CharTwo.add_eq_zero.mp h
          have hxq : (x : K) ^ q = (x : K) := (hk (x : K)).mp x.2
          have hsq : (μ ^ q) ^ q = μ ^ q := by rw [← hxμ]; exact hxq
          have h1 : μ ^ (q * q) = μ ^ q := by rw [pow_mul]; exact hsq
          rw [← sq q, hμqsq] at h1
          exact h1.symm
      have hmu2 : μ ^ 2 = 1 := by rw [← hμmul, hmuq, sq]
      have hdvd : orderOf μ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hmu2
      rw [hμord] at hdvd
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
      omega

private def l937z_sub_bMat {k : Type} [Field k] (n : ℕ) (a : k) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k :=
  Matrix.fromBlocks 0 1 1 (a • 1)

private lemma l937z_sub_add_self {k : Type} [Field k] [CharP k 2] {ι : Type}
    (X : Matrix ι ι k) : X + X = 0 := by
  ext i j
  simp [Matrix.add_apply, CharTwo.add_self_eq_zero]

private lemma l937z_sub_neg_one_eq_one {k : Type} [Field k] [CharP k 2] (n : ℕ) :
    (-(1 : Matrix (Fin n) (Fin n) k)) = 1 := by
  rw [neg_eq_iff_add_eq_zero]
  ext i j
  simp [Matrix.add_apply, Matrix.one_apply, CharTwo.add_self_eq_zero]

private lemma l937z_sub_bMat_sq_add {k : Type} [Field k] [CharP k 2] (n : ℕ) (a : k) :
    (l937z_sub_bMat n a) ^ 2 + a • (l937z_sub_bMat n a) = 1 := by
  rw [← Matrix.fromBlocks_one]
  rw [pow_two, l937z_sub_bMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_add, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp [l937z_sub_add_self]
  · simp [l937z_sub_add_self]
  · simp only [Matrix.mul_one, Matrix.mul_smul, smul_smul, add_assoc,
      l937z_sub_add_self, add_zero]

private lemma l937z_sub_bMat_mul {k : Type} [Field k] [CharP k 2] (n : ℕ) (a : k) :
    (l937z_sub_bMat n a) * (l937z_sub_bMat n a + a • 1) = 1 := by
  have hring : (l937z_sub_bMat n a) * (l937z_sub_bMat n a + a • 1) =
      (l937z_sub_bMat n a) ^ 2 + a • (l937z_sub_bMat n a) := by
    rw [pow_two, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  rw [hring, l937z_sub_bMat_sq_add]

private lemma l937z_sub_bMat_mul' {k : Type} [Field k] [CharP k 2] (n : ℕ) (a : k) :
    (l937z_sub_bMat n a + a • 1) * (l937z_sub_bMat n a) = 1 := by
  have hring : (l937z_sub_bMat n a + a • 1) * (l937z_sub_bMat n a) =
      (l937z_sub_bMat n a) ^ 2 + a • (l937z_sub_bMat n a) := by
    rw [pow_two, Matrix.add_mul, smul_mul, Matrix.one_mul]
  rw [hring, l937z_sub_bMat_sq_add]

private lemma l937z_sub_bMat_rel {k : Type} [Field k] [CharP k 2] (n : ℕ) (a : k) :
    (l937z_sub_bMat n a) ^ 2 + a • (l937z_sub_bMat n a) + 1 = 0 := by
  rw [l937z_sub_bMat_sq_add, l937z_sub_add_self]

private lemma l937z_sub_J_mul_J {k : Type} [Field k] [CharP k 2] (n : ℕ) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) *
      Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  conv_rhs => rw [← Matrix.fromBlocks_one]
  rw [l937z_sub_neg_one_eq_one n, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

private lemma l937z_sub_formAdj_one {k : Type} [Field k] [CharP k 2] (n : ℕ) :
    formAdj (RingHom.id k)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) 1 = 1 := by
  have hdet : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k).det :=
    Matrix.isUnit_det_of_right_inverse (l937z_sub_J_mul_J n)
  rw [formAdj, Matrix.map_one (RingHom.id k) rfl rfl, Matrix.transpose_one, Matrix.mul_one]
  exact Matrix.nonsing_inv_mul _ hdet

private lemma l937z_sub_bMat_mem {k : Type} [Field k] [CharP k 2] (n : ℕ) (a : k) :
    (l937z_sub_bMat n a)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * l937z_sub_bMat n a =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [l937z_sub_neg_one_eq_one n]
  rw [l937z_sub_bMat, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [l937z_sub_add_self]

private lemma l937z_su_b_exists {k : Type} [Field k] [CharP k 2] (n : ℕ) (a : k) :
    ∃ b : GL (Fin n ⊕ Fin n) k, b ∈ StatedSp n k ∧
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) = Matrix.fromBlocks 0 1 1 (a • 1) ∧
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) ^ 2 +
        a • (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) + 1 = 0 := by
  refine ⟨Units.mk (l937z_sub_bMat n a) (l937z_sub_bMat n a + a • 1)
    (l937z_sub_bMat_mul n a) (l937z_sub_bMat_mul' n a), ?_, rfl, ?_⟩
  · rw [Open.StatedAPI.mem_statedSp_iff]
    change (l937z_sub_bMat n a)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * l937z_sub_bMat n a =
      Matrix.fromBlocks 0 1 (-1) 0
    exact l937z_sub_bMat_mem n a
  · change (l937z_sub_bMat n a) ^ 2 + a • (l937z_sub_bMat n a) + 1 = 0
    exact l937z_sub_bMat_rel n a

private lemma l937z_su_blockCentralizer_one {k : Type} [Field k] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) k) (hb : b ∈ StatedSp n k) :
    glBlockCentralizer (StatedSp n k).subtype ({b} : Set (GL (Fin n ⊕ Fin n) k)) 1 =
      Subgroup.centralizer ({⟨b, hb⟩} : Set ↥(StatedSp n k)) := by
  ext g
  rw [glBlockCentralizer]
  simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, glFixing,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, -⟩ h hh
    apply Subtype.ext
    have hh' : (h : GL (Fin n ⊕ Fin n) k) = b := by rw [hh]
    simpa using h1 (h : GL (Fin n ⊕ Fin n) k) hh'
  · intro h1
    refine ⟨?_, ?_⟩
    · intro h hh
      rw [hh]
      exact congrArg Subtype.val (h1 ⟨b, hb⟩ rfl)
    · simp

private lemma l937z_su_prim {k : Type} [Field k] [CharP k 2] {n : ℕ} (hn : 1 ≤ n)
    (b : GL (Fin n ⊕ Fin n) k)
    (hfin : Module.finrank k
      ↥(Algebra.adjoin k (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) k)))) = 2)
    (hidem : ∀ e ∈ Algebra.adjoin k (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) k))),
      IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsPrimAdjIdemIn (RingHom.id k)
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
        (Algebra.adjoin k (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) k)))) 1 ∧
      IsPrimIdemIn (Algebra.adjoin k (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) k)))) 1 ∧
      blockDegree (Algebra.adjoin k (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) k)))) 1 = 2 := by
  set A : Subalgebra k (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) :=
    Algebra.adjoin k (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) k))) with hA
  have hone_mem : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) ∈ A := Subalgebra.one_mem A
  have hone_idem : IsIdempotentElem (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) :=
    IsIdempotentElem.one
  have hone_ne : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) ≠ 0 := by
    intro h
    let i : Fin n ⊕ Fin n := Sum.inl ⟨0, by omega⟩
    have h' : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) i i = 0 := by rw [h]; simp
    rw [Matrix.one_apply, if_pos rfl] at h'
    exact one_ne_zero h'
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hone_mem, hone_idem, hone_ne, l937z_sub_formAdj_one n,
      fun e' he' hidem' _ _ => hidem e' he' hidem'⟩
  · exact ⟨hone_mem, hone_idem, hone_ne, fun e' he' hidem' _ => hidem e' he' hidem'⟩
  · rw [blockDegree, LinearMap.mulRight_one, Submodule.map_id, hA]
    exact hfin

private lemma l937z_suc_quad_natDegree {k : Type} [Field k] (a : k) :
    (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 : Polynomial k).natDegree = 2 := by
  rw [show Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 =
    Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C 1 by
      simp [Polynomial.C_1]]
  exact Polynomial.natDegree_quadratic (by norm_num : (1 : k) ≠ 0)

private lemma l937z_suc_aeval_quad {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : k) (b : Matrix ι ι k) (hb : b ^ 2 + a • b + 1 = 0) :
    Polynomial.aeval b (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1) = 0 := by
  simpa [Polynomial.aeval_def, Algebra.smul_def] using hb

private lemma l937z_suc_adjoin_equiv {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (a : k)
    (hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 : Polynomial k))
    (b : Matrix ι ι k) (hb : b ^ 2 + a • b + 1 = 0) :
    Nonempty (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1) ≃ₐ[k]
      Algebra.adjoin k {b}) := by
  classical
  let p : Polynomial k := Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1
  let A : Subalgebra k (Matrix ι ι k) := Algebra.adjoin k {b}
  have hb' : Polynomial.aeval b p = 0 := by
    simpa [p] using l937z_suc_aeval_quad a b hb
  have hcommP : ({b} : Set (Matrix ι ι k)).Pairwise Commute := by
    intro x hx y hy _
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    exact Commute.refl _
  letI : CommRing A := by
    change CommRing (Algebra.adjoin k ({b} : Set (Matrix ι ι k)))
    exact Algebra.adjoinCommRingOfComm k hcommP
  have hbA : b ∈ A := Algebra.subset_adjoin (by simp)
  let x : A := ⟨b, hbA⟩
  have hx' : Polynomial.aeval x p = 0 := by
    apply Subtype.ext
    simpa [x] using hb'
  let φ : AdjoinRoot p →ₐ[k] A :=
    AdjoinRoot.liftAlgHom (S := k) p (Algebra.ofId k A) x (by
      simpa [Polynomial.aeval_def] using hx')
  haveI : Fact (Irreducible p) := ⟨by simpa [p] using hirr⟩
  have hφinj : Function.Injective φ := RingHom.injective φ.toRingHom
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : Matrix ι ι k) ∈
        (Polynomial.aeval (R := k) b : Polynomial k →ₐ[k] Matrix ι ι k).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact y.2
    obtain ⟨q, hq⟩ := hy
    refine ⟨(AdjoinRoot.mk p) q, ?_⟩
    apply Subtype.ext
    rw [AdjoinRoot.liftAlgHom_mk]
    change (Subalgebra.val A) (Polynomial.aeval (R := k) x q) = (y : Matrix ι ι k)
    have h1 : (Polynomial.aeval (R := k) b) q =
        (Subalgebra.val A) (Polynomial.aeval (R := k) x q) := by
      have h := congrArg (fun f : Polynomial k →ₐ[k] Matrix ι ι k => f q)
        (Polynomial.aeval_algHom (Subalgebra.val A) x)
      simpa using h
    rw [← h1]
    exact hq
  exact ⟨AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩⟩

private lemma l937z_su_adjoin_field {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (a : k)
    (hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 : Polynomial k))
    (b : Matrix ι ι k) (hb : b ^ 2 + a • b + 1 = 0) :
    Module.finrank k ↥(Algebra.adjoin k {b}) = 2 ∧
      ∀ e ∈ Algebra.adjoin k {b}, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  classical
  obtain ⟨e⟩ := l937z_suc_adjoin_equiv a hirr b hb
  haveI : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 :
      Polynomial k)) := ⟨hirr⟩
  have hpne : (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 : Polynomial k) ≠ 0 :=
    hirr.ne_zero
  have hpdeg : (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 :
      Polynomial k).natDegree = 2 := l937z_suc_quad_natDegree a
  have hdim : Module.finrank k
      (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1)) = 2 := by
    rw [(AdjoinRoot.powerBasis hpne).finrank, AdjoinRoot.powerBasis_dim hpne, hpdeg]
  constructor
  · calc Module.finrank k ↥(Algebra.adjoin k {b}) =
        Module.finrank k
          (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1)) :=
          e.toLinearEquiv.finrank_eq.symm
      _ = 2 := hdim
  · intro e0 he0 hidem
    have hidemA : IsIdempotentElem (⟨e0, he0⟩ : Algebra.adjoin k {b}) := by
      show (⟨e0, he0⟩ : Algebra.adjoin k {b}) * ⟨e0, he0⟩ = ⟨e0, he0⟩
      exact Subtype.ext hidem
    have hz : IsIdempotentElem (e.symm ⟨e0, he0⟩) := hidemA.map e.symm
    rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hz) with h0 | h1
    · left
      have hsub : (⟨e0, he0⟩ : Algebra.adjoin k {b}) = 0 := by
        have := congrArg e h0
        simpa using this
      exact Subtype.ext_iff.mp hsub
    · right
      have hsub : (⟨e0, he0⟩ : Algebra.adjoin k {b}) = 1 := by
        have := congrArg e h1
        simpa using this
      exact Subtype.ext_iff.mp hsub

private lemma l937z_su_orderOf_eq {k K : Type} [Field k] [Field K] [Algebra k K] {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (a : k)
    (hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1 : Polynomial k))
    (b : GL ι k) (hb : (b : Matrix ι ι k) ^ 2 + a • (b : Matrix ι ι k) + 1 = 0) (μ : K)
    (hμ : μ ^ 2 + algebraMap k K a * μ + 1 = 0) : orderOf b = orderOf μ := by
  classical
  let p : Polynomial k := Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + 1
  let A : Subalgebra k (Matrix ι ι k) := Algebra.adjoin k {(b : Matrix ι ι k)}
  have hb' : Polynomial.aeval (b : Matrix ι ι k) p = 0 := by
    simpa [p] using l937z_suc_aeval_quad a (b : Matrix ι ι k) hb
  have hμ' : Polynomial.eval₂ (algebraMap k K) μ p = 0 := by
    have h : Polynomial.aeval (R := k) μ p = 0 := by simpa [p] using hμ
    simpa [Polynomial.aeval_def] using h
  have hcommP : ({(b : Matrix ι ι k)} : Set (Matrix ι ι k)).Pairwise Commute := by
    intro x hx y hy _
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    exact Commute.refl _
  letI : CommRing A := by
    change CommRing (Algebra.adjoin k ({(b : Matrix ι ι k)} : Set (Matrix ι ι k)))
    exact Algebra.adjoinCommRingOfComm k hcommP
  have hbA : (b : Matrix ι ι k) ∈ A := Algebra.subset_adjoin (by simp)
  let x : A := ⟨(b : Matrix ι ι k), hbA⟩
  have hx' : Polynomial.aeval x p = 0 := by
    apply Subtype.ext
    simpa [x] using hb'
  let φ : AdjoinRoot p →ₐ[k] A :=
    AdjoinRoot.liftAlgHom (S := k) p (Algebra.ofId k A) x (by
      simpa [Polynomial.aeval_def] using hx')
  have hφroot : φ (AdjoinRoot.root p) = x := AdjoinRoot.liftAlgHom_root p _ x _
  haveI : Fact (Irreducible p) := ⟨by simpa [p] using hirr⟩
  have hφinj : Function.Injective φ := RingHom.injective φ.toRingHom
  let ψ : AdjoinRoot p →ₐ[k] K :=
    AdjoinRoot.liftAlgHom (S := k) p (Algebra.ofId k K) μ (by
      simpa using hμ')
  have hψroot : ψ (AdjoinRoot.root p) = μ := AdjoinRoot.liftAlgHom_root p _ μ _
  have hψinj : Function.Injective ψ := RingHom.injective ψ.toRingHom
  have hval_inj : Function.Injective (Subalgebra.val A) := by
    intro u v h
    exact Subtype.ext h
  have hxval : (Subalgebra.val A) x = (b : Matrix ι ι k) := rfl
  have hbx : orderOf b = orderOf x := by
    calc orderOf b = orderOf (b : Matrix ι ι k) := (orderOf_units).symm
      _ = orderOf ((Subalgebra.val A) x) := by rw [hxval]
      _ = orderOf x :=
        orderOf_injective ((Subalgebra.val A).toRingHom.toMonoidHom) hval_inj x
  have hφord : orderOf x = orderOf (AdjoinRoot.root p) := by
    have h := orderOf_injective (φ.toRingHom.toMonoidHom) hφinj (AdjoinRoot.root p)
    simpa [hφroot] using h
  have hψord : orderOf μ = orderOf (AdjoinRoot.root p) := by
    have h := orderOf_injective (ψ.toRingHom.toMonoidHom) hψinj (AdjoinRoot.root p)
    simpa [hψroot] using h
  calc orderOf b = orderOf x := hbx
    _ = orderOf (AdjoinRoot.root p) := hφord
    _ = orderOf μ := hψord.symm

private lemma l937z_sud_guFull_cond {E K : Type} [Field E] [Field K] (σ : E ≃+* K) (m Q : ℕ)
    (A : Matrix (Fin m) (Fin m) E) :
    ((A.map σ).map (· ^ Q))ᵀ * (A.map σ) = ((A.map (· ^ Q))ᵀ * A).map σ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_pow]

private lemma l937z_su_guFull_equiv {E K : Type} [Field E] [Field K] (σ : E ≃+* K) (m Q : ℕ) :
    Nonempty (↥(GUFull m Q E) ≃* ↥(GUFull m Q K)) := by
  let f : GL (Fin m) E ≃* GL (Fin m) K := Units.mapEquiv σ.mapMatrix.toMulEquiv
  have hcoe : ∀ A : GL (Fin m) E,
      ((f.toMonoidHom A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
        = (A : Matrix (Fin m) (Fin m) E).map σ := by
    intro A
    change ((Units.mapEquiv σ.mapMatrix.toMulEquiv A : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) = _
    rw [Units.coe_mapEquiv]
    exact RingEquiv.mapMatrix_apply σ (A : Matrix (Fin m) (Fin m) E)
  have hcoe_symm : ∀ B : GL (Fin m) K,
      ((f.symm B : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)
        = (B : Matrix (Fin m) (Fin m) K).map σ.symm := by
    intro B
    change ((Units.mapEquiv σ.mapMatrix.toMulEquiv).symm B : GL (Fin m) E) =
      (B : Matrix (Fin m) (Fin m) K).map σ.symm
    rw [Units.mapEquiv_symm, Units.coe_mapEquiv]
    exact RingEquiv.mapMatrix_apply σ.symm (B : Matrix (Fin m) (Fin m) K)
  have hset : f.toMonoidHom '' {A : GL (Fin m) E |
      ((A : Matrix (Fin m) (Fin m) E).map (· ^ Q))ᵀ * (A : Matrix (Fin m) (Fin m) E) = 1} =
      {A : GL (Fin m) K |
        ((A : Matrix (Fin m) (Fin m) K).map (· ^ Q))ᵀ * (A : Matrix (Fin m) (Fin m) K) = 1} := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      simp only [Set.mem_setOf_eq] at hA ⊢
      rw [hcoe A, l937z_sud_guFull_cond σ m Q (A : Matrix (Fin m) (Fin m) E), hA,
        Matrix.map_one σ (map_zero σ) (map_one σ)]
    · intro hB
      refine ⟨f.symm B, ?_, f.apply_symm_apply B⟩
      simp only [Set.mem_setOf_eq] at hB ⊢
      rw [hcoe_symm B, l937z_sud_guFull_cond σ.symm m Q (B : Matrix (Fin m) (Fin m) K), hB,
        Matrix.map_one σ.symm (map_zero σ.symm) (map_one σ.symm)]
  have hmap : (GUFull m Q E).map f.toMonoidHom = GUFull m Q K := by
    rw [GUFull, GUFull, MonoidHom.map_closure, hset]
  exact ⟨(MulEquiv.subgroupMap f (GUFull m Q E)).trans (MulEquiv.subgroupCongr hmap)⟩

theorem exists_guFull_equiv_centralizer_statedSp {K : Type} [Field K] [Finite K] [CharP K 2]
    (q n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = q ^ 2) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2), Nat.card k = q ∧
      ∃ t : ↥(StatedSp n k), orderOf t = q + 1 ∧
        Nonempty (↥(GUFull n q K) ≃* ↥(Subgroup.centralizer ({t} : Set ↥(StatedSp n k)))) := by
  classical
  have h2K : 2 ≤ Nat.card K := by
    have h := Finite.one_lt_card (α := K)
    omega
  have hq2 : 2 ≤ q := by
    have hsq : 2 ≤ q ^ 2 := by rw [← hK]; exact h2K
    rcases lt_or_ge q 2 with h | h
    · interval_cases q <;> simp_all
    · exact h
  obtain ⟨k₀, hk₀card, hk₀⟩ := l937z_su_subfield q hq2 hK
  haveI : Finite ↥k₀ := Subtype.finite
  haveI : CharP ↥k₀ 2 := Subfield.charP k₀ 2
  haveI : Fintype ↥k₀ := Fintype.ofFinite ↥k₀
  obtain ⟨μ, a, hμord, _, hμrel, hirr⟩ := l937z_su_mu_data q hq2 hK k₀ hk₀
  obtain ⟨b, hb, _, hbrel⟩ := l937z_su_b_exists (k := ↥k₀) n a
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
  have hμ' : μ ^ 2 + algebraMap ↥k₀ K a * μ + 1 = 0 := by
    simpa [Subfield.algebraMap_ofSubfield] using hμrel
  have hordb : orderOf b = q + 1 := by
    rw [l937z_su_orderOf_eq a hirr b hbrel μ hμ', hμord]
  obtain ⟨hfin, hidem⟩ :=
    l937z_su_adjoin_field a hirr (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥k₀) hbrel
  have hfin' : Module.finrank ↥k₀
      ↥(Algebra.adjoin ↥k₀ (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) ↥k₀)))) = 2 := by
    rw [show Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) ↥k₀)) = {↑b} from Set.image_singleton]
    exact hfin
  have hidem' : ∀ e ∈ Algebra.adjoin ↥k₀
      (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) ↥k₀))),
      IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    rw [show Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) ↥k₀)) = {↑b}
        from Set.image_singleton] at he
    exact hidem e he
  obtain ⟨hε, hp, hdeg⟩ := l937z_su_prim hn b hfin' hidem'
  have hodd : Odd (orderOf b) := by
    rw [hordb]
    obtain ⟨j, hjne, hqj⟩ := l937z_su_exists_pow_two q hq2 hK
    rw [hqj]
    cases j with
    | zero => exact absurd rfl hjne
    | succ j =>
        exact (show Even (2 ^ (j + 1)) from by
          rw [pow_succ]; exact ⟨2 ^ j, by ring⟩).add_one
  have h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥k₀) * 1 ≠ 1 := by
    intro h
    have hb1 : b = 1 := Units.ext (by simpa using h)
    have hone : orderOf b = 1 := by rw [hb1, orderOf_one]
    rw [hordb] at hone
    omega
  obtain ⟨d, m, E, hEfield, hEfin, hd1, hEcard, hrank, hblock, hiso⟩ :=
    blockGroup_iso_Sp_unitary b hb hodd hε hp h1
  have hd_eq : d = 1 := by
    have h2d : 2 * d = 2 := by rw [← hblock, hdeg]
    omega
  have hfinrank : Module.finrank ↥k₀
      (LinearMap.range (Matrix.toLin' (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥k₀)))
      = 2 * n := by
    rw [Matrix.toLin'_one, LinearMap.range_id, finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hm_eq : m = n := by
    have h1 : 2 * d * m = 2 * m := by simp [hd_eq]
    have h2 : 2 * m = 2 * n := by rw [← h1, hrank, hfinrank]
    omega
  subst hd_eq
  rw [hm_eq] at hiso
  have hkcard : Fintype.card ↥k₀ = q := by
    rw [← Nat.card_eq_fintype_card, hk₀card]
  rw [pow_one, hkcard] at hiso
  have hEcardK : @Fintype.card E hEfin = @Fintype.card K (Fintype.ofFinite K) := by
    rw [hEcard, pow_one, hkcard, ← hK]
    exact @Nat.card_eq_fintype_card K (Fintype.ofFinite K)
  let σ := @FiniteField.ringEquivOfCardEq E K hEfield _ hEfin (Fintype.ofFinite K) hEcardK
  have hgu := (@l937z_su_guFull_equiv E K hEfield _ σ n q).some.symm
  obtain ⟨isoE⟩ := hiso
  have hsub := l937z_su_blockCentralizer_one b hb
  refine ⟨↥k₀, inferInstance, inferInstance, inferInstance, hk₀card, ⟨⟨b, hb⟩, ?_, ?_⟩⟩
  · rw [Subgroup.orderOf_mk]; exact hordb
  · exact ⟨hgu.trans (isoE.symm.trans (MulEquiv.subgroupCongr hsub))⟩

theorem statedSU_le_guFull {K : Type} [Field K] (n q : ℕ) :
    StatedSU n q K ≤ GUFull n q K := by
  rw [StatedSU, GUFull]
  exact Subgroup.closure_mono (fun A hA => hA.2)

end CFSG.StandardType.SporadicShape

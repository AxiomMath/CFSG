module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteOrderAverages
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoOneLinear

public section

namespace CFSG.StandardType.TableC

open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.ClassicalBlocks
open CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def fixIdem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (p : ℕ)
    (s : GL ι F) : Matrix ι ι F :=
  ((p : F)⁻¹) • ∑ i ∈ Finset.range p, ((s : Matrix ι ι F) ^ i)

@[expose] noncomputable def trivBlock (n : ℕ) (F : Type) [Field F] (p : ℕ)
    (s : ↥(StatedSp n F)) : Subgroup ↥(StatedSp n F) :=
  glBlockCentralizer (StatedSp n F).subtype
    ({(s : GL (Fin n ⊕ Fin n) F)} : Set (GL (Fin n ⊕ Fin n) F))
    (fixIdem p (s : GL (Fin n ⊕ Fin n) F))

private abbrev tblJ (n : ℕ) (F : Type) [Field F] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.fromBlocks 0 1 (-1) 0

private lemma tblJ_mul_self {n : ℕ} {F : Type} [Field F] :
    tblJ n F * tblJ n F = -1 := by
  unfold tblJ
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero]
  rw [show (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.fromBlocks (-1) 0 0 (-1) by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp]

private lemma tblJ_isUnit_det {n : ℕ} {F : Type} [Field F] :
    IsUnit (tblJ n F).det := by
  have h1 : tblJ n F * (-(tblJ n F)) = 1 := by
    rw [Matrix.mul_neg, tblJ_mul_self, neg_neg]
  have h2 : (-(tblJ n F)) * tblJ n F = 1 := by
    rw [Matrix.neg_mul, tblJ_mul_self, neg_neg]
  exact (Matrix.isUnit_iff_isUnit_det (tblJ n F)).mp
    (isUnit_iff_exists.mpr ⟨-(tblJ n F), h1, h2⟩)

private lemma tbl_coe_pow {n : ℕ} {F : Type} [Field F] (b : GL (Fin n ⊕ Fin n) F) (i : ℕ) :
    ((b ^ i : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i :=
  Units.val_pow_eq_pow_val b i

private lemma tbl_geom_sum_mul {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hpow : b ^ p = 1) :
    (∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) *
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      ∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i :=
  finiteOrder_geometric_sum_fixes_right p (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (by
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one])

private lemma tbl_geom_sum_comm {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) :
    Commute (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) :=
  Commute.sum_right _ _ _
    (fun i _ => (Commute.refl (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).pow_right i)

private lemma tbl_geom_sum_mul_left {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hpow : b ^ p = 1) :
    (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) =
      ∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i := by
  rw [(tbl_geom_sum_comm (p := p) b).eq]
  exact tbl_geom_sum_mul b hpow

private lemma tbl_geom_sum_pow_mul {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hpow : b ^ p = 1) (i : ℕ) :
    (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i *
        (∑ j ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ j) =
      ∑ j ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ j := by
  induction i with
  | zero => rw [pow_zero, Matrix.one_mul]
  | succ i ih => rw [pow_succ', Matrix.mul_assoc, ih, tbl_geom_sum_mul_left b hpow]

private lemma tbl_fixIdem_idem {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hpow : b ^ p = 1) (hc : (p : F) ≠ 0) :
    IsIdempotentElem (fixIdem p b) := by
  have hSnat : (∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) *
      (∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) =
      p • ∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i := by
    rw [Finset.sum_mul]
    simp only [tbl_geom_sum_pow_mul b hpow]
    rw [Finset.sum_const, Finset.card_range]
  have hS : (∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) *
      (∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) =
      (p : F) • ∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i := by
    rw [hSnat]
    exact (Nat.cast_smul_eq_nsmul F p _).symm
  unfold fixIdem
  change (((p : F)⁻¹) • ∑ i ∈ Finset.range p,
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) *
      (((p : F)⁻¹) • ∑ i ∈ Finset.range p,
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) =
      ((p : F)⁻¹) • ∑ i ∈ Finset.range p,
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i
  rw [Matrix.smul_mul, Matrix.mul_smul, hS, smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]

private lemma tbl_fixIdem_mul_left {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hpow : b ^ p = 1) :
    (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * fixIdem p b = fixIdem p b := by
  unfold fixIdem
  rw [Matrix.mul_smul, tbl_geom_sum_mul_left b hpow]

private lemma tbl_pow_mul_fixIdem {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hpow : b ^ p = 1) (i : ℕ) :
    (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i * fixIdem p b = fixIdem p b := by
  induction i with
  | zero => rw [pow_zero, Matrix.one_mul]
  | succ i ih => rw [pow_succ', Matrix.mul_assoc, ih, tbl_fixIdem_mul_left b hpow]

private lemma tbl_geom_sum_inv_eq {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hpow : b ^ p = 1) :
    (∑ i ∈ Finset.range p, (((b⁻¹ : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i)) =
      ∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have hpow' : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  have hshift : (∑ j ∈ Finset.range p,
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ (j + 1)) =
      ∑ j ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ j := by
    have h1 := Finset.sum_range_succ
      (fun k => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ k) p
    have h2 := Finset.sum_range_succ'
      (fun k => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ k) p
    rw [hpow'] at h1
    rw [pow_zero] at h2
    exact (add_right_cancel (h1.symm.trans h2)).symm
  rw [← Finset.sum_range_reflect
    (fun i => (((b⁻¹ : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i)) p]
  rw [← hshift]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mem_range] at hj
  have hle : p - 1 - j ≤ p := by omega
  have hk : (b⁻¹ : GL (Fin n ⊕ Fin n) F) ^ (p - 1 - j) = b ^ (j + 1) := by
    rw [inv_pow]
    have hmul : b ^ (p - 1 - j) * b ^ (p - (p - 1 - j)) = 1 := by
      rw [← pow_add, Nat.add_sub_of_le hle, hpow]
    have hsub : p - (p - 1 - j) = j + 1 := by omega
    rw [hsub] at hmul
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  have := congrArg (fun u : GL (Fin n ⊕ Fin n) F =>
    (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) hk
  simpa [Units.val_pow_eq_pow_val] using this

private lemma tbl_formAdj_fixIdem {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hb : b ∈ StatedSp n F) (hpow : b ^ p = 1) :
    formAdj (RingHom.id F) (tblJ n F) (fixIdem p b) = fixIdem p b := by
  have hJdet : IsUnit (tblJ n F).det := tblJ_isUnit_det
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F),
      formAdj (RingHom.id F) (tblJ n F) (∑ i ∈ s, f i) =
        ∑ i ∈ s, formAdj (RingHom.id F) (tblJ n F) (f i) := by
    intro s f
    refine Finset.induction_on s ?_ ?_
    · simp [formAdj]
    · intro a s has ih
      rw [Finset.sum_insert has, Finset.sum_insert has, Geo.formAdj_add, ih]
  have hiso : ∀ i : ℕ, formAdj (RingHom.id F) (tblJ n F)
      ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) =
      (((b⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) := by
    intro i
    have hbpow : b ^ i ∈ StatedSp n F := Subgroup.pow_mem _ hb i
    have hisom : ((b ^ i : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).transpose * tblJ n F *
        ((b ^ i : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        tblJ n F := CFSG.Open.StatedAPI.mem_statedSp_iff.mp hbpow
    have h := Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hJdet (b ^ i) (by
      rw [show (⇑(RingHom.id F) : F → F) = id from rfl, Matrix.map_id]
      simpa only [tbl_coe_pow] using hisom)
    rw [show (b ^ i)⁻¹ = (b⁻¹) ^ i from (inv_pow b i).symm] at h
    simpa only [tbl_coe_pow, Units.val_pow_eq_pow_val] using h
  have hsum' : formAdj (RingHom.id F) (tblJ n F)
      (∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) =
      ∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i := by
    rw [hsum]
    simpa only [hiso] using tbl_geom_sum_inv_eq b hpow
  unfold fixIdem
  rw [Geo.formAdj_smul, hsum']
  rfl

private lemma tbl_fixIdem_mem_adjoin {n : ℕ} {F : Type} [Field F] (p : ℕ)
    (b : GL (Fin n ⊕ Fin n) F) :
    fixIdem p b ∈ Algebra.adjoin F (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) F))) := by
  unfold fixIdem
  refine Subalgebra.smul_mem _ ?_ _
  refine Subalgebra.sum_mem _ ?_
  intro i _
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) i

private lemma tbl_aeval_mul_fixIdem {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hpow : b ^ p = 1) (q : Polynomial F) :
    Polynomial.aeval (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) q * fixIdem p b =
      (Polynomial.eval (1 : F) q) • fixIdem p b := by
  refine Polynomial.induction_on q ?hC ?hadd ?hmul
  · intro a
    rw [Polynomial.aeval_C, Polynomial.eval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul]
  · intro q r hq hr
    rw [Polynomial.aeval_add, Polynomial.eval_add, Matrix.add_mul, hq, hr, add_smul]
  · intro k a _
    have h1 : Polynomial.aeval (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Polynomial.C a * Polynomial.X ^ (k + 1)) =
        a • (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ (k + 1) := by
      rw [Polynomial.aeval_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
    have h2 : Polynomial.eval (1 : F) (Polynomial.C a * Polynomial.X ^ (k + 1)) = a := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        one_pow, mul_one]
    rw [h1, h2, Matrix.smul_mul, tbl_pow_mul_fixIdem b hpow]

private lemma tbl_fixIdem_prim {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b : GL (Fin n ⊕ Fin n) F) (hpow : b ^ p = 1)
    (hid : IsIdempotentElem (fixIdem p b)) (hne : fixIdem p b ≠ 0) :
    ∀ e' ∈ Algebra.adjoin F (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) F))),
      IsIdempotentElem e' → formAdj (RingHom.id F) (tblJ n F) e' = e' →
      e' * fixIdem p b = e' →
      e' = 0 ∨ e' = fixIdem p b := by
  intro e' he'A hidem _ he'
  have he'A' : e' ∈ Algebra.adjoin F
      ({(b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)} :
        Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) := by
    simpa only [Set.image_singleton] using he'A
  rw [Algebra.adjoin_singleton_eq_range_aeval F
    (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)] at he'A'
  obtain ⟨q, hq⟩ := he'A'
  rw [← hq] at he' hidem ⊢
  have heq : (Polynomial.aeval (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).toRingHom q =
      (Polynomial.eval (1 : F) q) • fixIdem p b := by
    rw [← he']
    exact tbl_aeval_mul_fixIdem b hpow q
  have hidem' : IsIdempotentElem
      ((Polynomial.eval (1 : F) q) • fixIdem p b) := by
    rw [← heq]; exact hidem
  have hcoef : (Polynomial.eval (1 : F) q) * ((Polynomial.eval (1 : F) q) - 1) = 0 := by
    have h := hidem'.eq
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hid.eq] at h
    have hzero : ((Polynomial.eval (1 : F) q) * ((Polynomial.eval (1 : F) q) - 1)) •
        fixIdem p b = 0 := by
      rw [show (Polynomial.eval (1 : F) q) * ((Polynomial.eval (1 : F) q) - 1) =
        (Polynomial.eval (1 : F) q) * (Polynomial.eval (1 : F) q) - Polynomial.eval (1 : F) q
        by ring, sub_smul, h, sub_self]
    by_contra hc
    have hex : ∃ i j, fixIdem p b i j ≠ 0 := by
      by_contra h
      apply hne
      ext i j
      by_contra hij
      exact h ⟨i, j, hij⟩
    obtain ⟨i, j, hij⟩ := hex
    have hentry := congrFun (congrFun hzero i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hentry
    exact hc ((mul_eq_zero.mp hentry).resolve_right hij)
  rcases mul_eq_zero.mp hcoef with h0 | h1
  · exact Or.inl (by rw [heq, h0, zero_smul])
  · exact Or.inr (by rw [heq, sub_eq_zero.mp h1, one_smul])

private lemma tbl_rank_eq_finrank {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    (M : Matrix m m F) :
    M.rank = Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
  rw [Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun F m) (Pi.basisFun F m),
    Matrix.toLin_eq_toLin']

private def tblBlkVal {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) : Matrix ι ι F :=
  (m : Matrix ι ι F) * ε + (1 - ε)

private def tblBlkInvVal {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) : Matrix ι ι F :=
  ((m⁻¹ : GL ι F) : Matrix ι ι F) * ε + (1 - ε)

private lemma tbl_eps_mul_one_sub {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (h : IsIdempotentElem ε) : ε * (1 - ε) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, h.eq, sub_self]

private lemma tbl_one_sub_mul_eps {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (h : IsIdempotentElem ε) : (1 - ε) * ε = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, h.eq, sub_self]

private lemma tbl_one_sub_mul_one_sub {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (h : IsIdempotentElem ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [Matrix.mul_sub, Matrix.mul_one, tbl_one_sub_mul_eps h, sub_zero]

private lemma tbl_blkVal_fixes {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) (hid : IsIdempotentElem ε) :
    tblBlkVal m ε * (1 - ε) = 1 - ε := by
  rw [tblBlkVal, Matrix.add_mul, Matrix.mul_assoc, tbl_eps_mul_one_sub hid, Matrix.mul_zero,
    zero_add, tbl_one_sub_mul_one_sub hid]

private lemma tbl_inv_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) {ε : Matrix ι ι F}
    (hm : (m : Matrix ι ι F) * ε = ε * (m : Matrix ι ι F)) :
    (((m⁻¹ : GL ι F)) : Matrix ι ι F) * ε = ε * (((m⁻¹ : GL ι F)) : Matrix ι ι F) := by
  have hmm : (m : Matrix ι ι F) * (((m⁻¹ : GL ι F)) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hm'm : (((m⁻¹ : GL ι F)) : Matrix ι ι F) * (m : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (((m⁻¹ : GL ι F)) : Matrix ι ι F) * ε
      = (((m⁻¹ : GL ι F)) : Matrix ι ι F) * ε *
          ((m : Matrix ι ι F) * (((m⁻¹ : GL ι F)) : Matrix ι ι F)) := by
        rw [hmm, Matrix.mul_one]
    _ = (((m⁻¹ : GL ι F)) : Matrix ι ι F) * (ε * (m : Matrix ι ι F)) *
          (((m⁻¹ : GL ι F)) : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
    _ = (((m⁻¹ : GL ι F)) : Matrix ι ι F) * ((m : Matrix ι ι F) * ε) *
          (((m⁻¹ : GL ι F)) : Matrix ι ι F) := by rw [← hm]
    _ = ε * (((m⁻¹ : GL ι F)) : Matrix ι ι F) := by
        rw [← Matrix.mul_assoc (((m⁻¹ : GL ι F)) : Matrix ι ι F)
              (m : Matrix ι ι F) ε, hm'm, Matrix.one_mul]

private lemma tbl_blk_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (hid : IsIdempotentElem ε)
    {p q : Matrix ι ι F} (hq : q * ε = ε * q) :
    (p * ε + (1 - ε)) * (q * ε + (1 - ε)) = (p * q) * ε + (1 - ε) := by
  have hεε : ε * ε = ε := hid.eq
  have hp1 : p * ε * (1 - ε) = 0 := by
    rw [Matrix.mul_assoc, tbl_eps_mul_one_sub hid, Matrix.mul_zero]
  have hq1 : (1 - ε) * q = q * (1 - ε) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hq]
  have h1q : (1 - ε) * (q * ε) = 0 := by
    rw [← Matrix.mul_assoc, hq1, Matrix.mul_assoc, tbl_one_sub_mul_eps hid, Matrix.mul_zero]
  have hpq : (p * ε) * (q * ε) = (p * q) * ε := by
    rw [Matrix.mul_assoc p ε, ← Matrix.mul_assoc ε q ε, ← hq, Matrix.mul_assoc q ε ε, hεε,
        ← Matrix.mul_assoc p q ε]
  calc (p * ε + (1 - ε)) * (q * ε + (1 - ε))
      = (p * ε) * (q * ε) + (p * ε) * (1 - ε) +
          ((1 - ε) * (q * ε) + (1 - ε) * (1 - ε)) := by
        rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    _ = (p * q) * ε + 0 + (0 + (1 - ε)) := by
        rw [hpq, hp1, h1q, tbl_one_sub_mul_one_sub hid]
    _ = (p * q) * ε + (1 - ε) := by abel

private lemma tbl_blk_val_mul_inv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) (hid : IsIdempotentElem ε)
    (hm : (m : Matrix ι ι F) * ε = ε * (m : Matrix ι ι F)) :
    tblBlkVal m ε * tblBlkInvVal m ε = 1 := by
  have hmm : (m : Matrix ι ι F) * (((m⁻¹ : GL ι F)) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [tblBlkVal, tblBlkInvVal,
      tbl_blk_mul hid (tbl_inv_comm m hm), hmm, Matrix.one_mul,
      ← add_sub_assoc, add_sub_cancel_left]

private lemma tbl_blk_inv_mul_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) (hid : IsIdempotentElem ε)
    (hm : (m : Matrix ι ι F) * ε = ε * (m : Matrix ι ι F)) :
    tblBlkInvVal m ε * tblBlkVal m ε = 1 := by
  have hm'm : (((m⁻¹ : GL ι F)) : Matrix ι ι F) * (m : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [tblBlkVal, tblBlkInvVal,
      tbl_blk_mul hid hm, hm'm, Matrix.one_mul,
      ← add_sub_assoc, add_sub_cancel_left]

private noncomputable def tblBlk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) (hid : IsIdempotentElem ε)
    (hm : (m : Matrix ι ι F) * ε = ε * (m : Matrix ι ι F)) : GL ι F :=
  Units.mk (tblBlkVal m ε) (tblBlkInvVal m ε)
    (tbl_blk_val_mul_inv m ε hid hm) (tbl_blk_inv_mul_val m ε hid hm)

private lemma tbl_blk_mem_statedSp {n : ℕ} {F : Type} [Field F]
    (m : GL (Fin n ⊕ Fin n) F) (hm : m ∈ StatedSp n F)
    (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (hid : IsIdempotentElem ε)
    (hcomm : (m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε =
      ε * (m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
    (hst : formAdj (RingHom.id F) (tblJ n F) ε = ε) :
    tblBlk m ε hid hcomm ∈ StatedSp n F := by
  have hJdet : IsUnit (tblJ n F).det := tblJ_isUnit_det
  have hcomm' := tbl_inv_comm m hcomm
  have hm_inv : formAdj (RingHom.id F) (tblJ n F) (m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    refine Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hJdet m ?_
    simpa [tblJ] using (CFSG.Open.StatedAPI.mem_statedSp_iff.mp hm)
  have h1e : formAdj (RingHom.id F) (tblJ n F) (1 - ε) = 1 - ε := by
    have h := Geo.formAdj_add (RingHom.id F) (tblJ n F) (1 - ε) ε
    rw [sub_add_cancel, Geo.formAdj_one (RingHom.id F) hJdet, hst] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  have hformX : formAdj (RingHom.id F) (tblJ n F) (tblBlkVal m ε) =
      tblBlkInvVal m ε := by
    rw [tblBlkVal, tblBlkInvVal, Geo.formAdj_add,
        Geo.formAdj_mul (RingHom.id F) hJdet, hm_inv, hst, h1e, ← hcomm']
  have hinv_val : tblBlkInvVal m ε * tblBlkVal m ε = 1 :=
    tbl_blk_inv_mul_val m ε hid hcomm
  have hJJ : tblJ n F * (tblJ n F)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJdet
  have hJform : (tblJ n F)⁻¹ * Matrix.transpose (tblBlkVal m ε) * tblJ n F =
      tblBlkInvVal m ε := hformX
  have hcoee : (tblBlk m ε hid hcomm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      tblBlkVal m ε := rfl
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff, hcoee]
  have h1 : Matrix.transpose (tblBlkVal m ε) * tblJ n F =
      tblJ n F * tblBlkInvVal m ε := by
    calc Matrix.transpose (tblBlkVal m ε) * tblJ n F
        = 1 * (Matrix.transpose (tblBlkVal m ε) * tblJ n F) := (Matrix.one_mul _).symm
      _ = (tblJ n F * (tblJ n F)⁻¹) *
            (Matrix.transpose (tblBlkVal m ε) * tblJ n F) := by rw [hJJ]
      _ = tblJ n F * ((tblJ n F)⁻¹ * Matrix.transpose (tblBlkVal m ε) *
            tblJ n F) := by simp only [Matrix.mul_assoc]
      _ = tblJ n F * tblBlkInvVal m ε := by rw [hJform]
  calc Matrix.transpose (tblBlkVal m ε) * tblJ n F * tblBlkVal m ε
      = (tblJ n F * tblBlkInvVal m ε) * tblBlkVal m ε := by rw [h1]
    _ = tblJ n F * (tblBlkInvVal m ε * tblBlkVal m ε) := by rw [Matrix.mul_assoc]
    _ = tblJ n F * 1 := by rw [hinv_val]
    _ = tblJ n F := Matrix.mul_one _

private lemma tbl_eq_blkVal {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    (ε : Matrix ι ι F) (H : Matrix ι ι F) (hfix : H * (1 - ε) = 1 - ε) :
    H = H * ε + (1 - ε) := by
  calc H = H * 1 := (Matrix.mul_one H).symm
    _ = H * (ε + (1 - ε)) := by rw [add_sub_cancel]
    _ = H * ε + H * (1 - ε) := by rw [Matrix.mul_add]
    _ = H * ε + (1 - ε) := by rw [hfix]

private lemma tbl_blk_comm {n : ℕ} {F : Type} [Field F]
    (b g : GL (Fin n ⊕ Fin n) F) (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hgb : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
    (hεb : ε * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε) :
    tblBlkVal g ε * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * tblBlkVal g ε := by
  unfold tblBlkVal
  have hGε : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε *
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε) := by
    rw [Matrix.mul_assoc, hεb, ← Matrix.mul_assoc, hgb, Matrix.mul_assoc]
  have h1ε : (1 - ε) * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (1 - ε) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hεb]
  calc ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε)) *
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      = (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε *
          (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) + (1 - ε) *
          (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by rw [Matrix.add_mul]
    _ = (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε) +
          (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (1 - ε) := by rw [hGε, h1ε]
    _ = (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε)) := by
        rw [Matrix.mul_add]

private lemma tbl_conj_fixes {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {ε : Matrix ι ι F} (k h : GL ι F)
    (hkε : (k : Matrix ι ι F) * ε = ε * (k : Matrix ι ι F))
    (hhfix : (h : Matrix ι ι F) * (1 - ε) = 1 - ε) :
    (k : Matrix ι ι F) * (h : Matrix ι ι F) * ((k⁻¹ : GL ι F) : Matrix ι ι F) *
        (1 - ε) = 1 - ε := by
  have hk_inv : (k : Matrix ι ι F) * ((k⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hk1 : (k : Matrix ι ι F) * (1 - ε) = (1 - ε) * (k : Matrix ι ι F) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hkε]
  have hk'ε : ((k⁻¹ : GL ι F) : Matrix ι ι F) * ε =
      ε * ((k⁻¹ : GL ι F) : Matrix ι ι F) := tbl_inv_comm k hkε
  have hk1' : ((k⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε) =
      (1 - ε) * ((k⁻¹ : GL ι F) : Matrix ι ι F) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hk'ε]
  calc (k : Matrix ι ι F) * (h : Matrix ι ι F) * ((k⁻¹ : GL ι F) : Matrix ι ι F) *
        (1 - ε)
      = (k : Matrix ι ι F) * (h : Matrix ι ι F) *
          (((k⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε)) := by noncomm_ring
    _ = (k : Matrix ι ι F) * (h : Matrix ι ι F) *
          ((1 - ε) * ((k⁻¹ : GL ι F) : Matrix ι ι F)) := by rw [hk1']
    _ = (k : Matrix ι ι F) * ((h : Matrix ι ι F) * (1 - ε)) *
          ((k⁻¹ : GL ι F) : Matrix ι ι F) := by noncomm_ring
    _ = (k : Matrix ι ι F) * (1 - ε) * ((k⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hhfix]
    _ = ((k : Matrix ι ι F) * (1 - ε)) * ((k⁻¹ : GL ι F) : Matrix ι ι F) := by noncomm_ring
    _ = ((1 - ε) * (k : Matrix ι ι F)) * ((k⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hk1]
    _ = (1 - ε) := by
        rw [Matrix.mul_assoc, hk_inv, Matrix.mul_one]

private lemma tbl_conj_fixes_inv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {ε : Matrix ι ι F} (G L : GL ι F)
    (hGε : (G : Matrix ι ι F) * ε = ε * (G : Matrix ι ι F))
    (hLfix : (L : Matrix ι ι F) * (1 - ε) = 1 - ε) :
    ((G⁻¹ : GL ι F) : Matrix ι ι F) * (L : Matrix ι ι F) * (G : Matrix ι ι F) *
        (1 - ε) = 1 - ε := by
  have hG_inv : ((G⁻¹ : GL ι F) : Matrix ι ι F) * (G : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hG1 : (G : Matrix ι ι F) * (1 - ε) = (1 - ε) * (G : Matrix ι ι F) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hGε]
  have hGε' : ((G⁻¹ : GL ι F) : Matrix ι ι F) * ε =
      ε * ((G⁻¹ : GL ι F) : Matrix ι ι F) := tbl_inv_comm G hGε
  have hG1' : ((G⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε) =
      (1 - ε) * ((G⁻¹ : GL ι F) : Matrix ι ι F) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hGε']
  calc ((G⁻¹ : GL ι F) : Matrix ι ι F) * (L : Matrix ι ι F) * (G : Matrix ι ι F) *
        (1 - ε)
      = ((G⁻¹ : GL ι F) : Matrix ι ι F) * (L : Matrix ι ι F) *
          ((G : Matrix ι ι F) * (1 - ε)) := by noncomm_ring
    _ = ((G⁻¹ : GL ι F) : Matrix ι ι F) * (L : Matrix ι ι F) *
          ((1 - ε) * (G : Matrix ι ι F)) := by rw [hG1]
    _ = ((G⁻¹ : GL ι F) : Matrix ι ι F) * ((L : Matrix ι ι F) * (1 - ε)) *
          (G : Matrix ι ι F) := by noncomm_ring
    _ = ((G⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε) * (G : Matrix ι ι F) := by rw [hLfix]
    _ = (((G⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε)) * (G : Matrix ι ι F) := by noncomm_ring
    _ = ((1 - ε) * ((G⁻¹ : GL ι F) : Matrix ι ι F)) * (G : Matrix ι ι F) := by rw [hG1']
    _ = (1 - ε) := by
        rw [Matrix.mul_assoc, hG_inv, Matrix.mul_one]

private lemma tbl_coe_mem_centralizer_singleton {n : ℕ} {F : Type} [Field F]
    (s x : ↥(StatedSp n F)) :
    (x : GL (Fin n ⊕ Fin n) F) ∈ Subgroup.centralizer
        ({(s : GL (Fin n ⊕ Fin n) F)} : Set (GL (Fin n ⊕ Fin n) F)) ↔
      x ∈ Subgroup.centralizer ({s} : Set ↥(StatedSp n F)) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    apply Subtype.ext
    have := h (s : GL (Fin n ⊕ Fin n) F) (Set.mem_singleton _)
    simpa only [Subgroup.coe_mul] using this
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have := congrArg (fun z : ↥(StatedSp n F) => (z : GL (Fin n ⊕ Fin n) F))
      (h s (Set.mem_singleton _))
    simpa only [Subgroup.coe_mul] using this


private lemma tbl_fixIdem_comm_of_comm {n : ℕ} {F : Type} [Field F] {p : ℕ}
    (b g : GL (Fin n ⊕ Fin n) F) (h : Commute g b) :
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * fixIdem p b =
      fixIdem p b * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  have hgb : Commute (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    show (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    simpa only [Units.val_mul] using congrArg Units.val h.eq
  have hcomm : Commute (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (∑ i ∈ Finset.range p, (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ i) :=
    Commute.sum_right _ _ _ (fun i _ => hgb.pow_right i)
  unfold fixIdem
  rw [Matrix.mul_smul, Matrix.smul_mul, hcomm.eq]

theorem trivialBlock_PSp (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (s : ↥(StatedSp n F)) (hs : s ^ p = 1) :
    ∃ m : ℕ, 2 * m = Matrix.rank (fixIdem p (s : GL (Fin n ⊕ Fin n) F)) ∧
      Nonempty (↥(trivBlock n F p s) ≃* ↥(StatedSp m F)) ∧
      Subgroup.Normal ((trivBlock n F p s).subgroupOf
        (Subgroup.centralizer ({s} : Set ↥(StatedSp n F)))) ∧
      ∀ g : ↥(StatedSp n F), Commute g s →
        ∃ r ∈ trivBlock n F p s, ∀ l ∈ trivBlock n F p s, g⁻¹ * l * g = r⁻¹ * l * r := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let b : GL (Fin n ⊕ Fin n) F := (s : GL (Fin n ⊕ Fin n) F)
  have hb : b ∈ StatedSp n F := s.2
  have hpow : b ^ p = 1 := by
    have h := congrArg (fun x : ↥(StatedSp n F) => (x : GL (Fin n ⊕ Fin n) F)) hs
    simpa only [b, Subgroup.coe_pow, Subgroup.coe_one] using h
  have hodd : Odd (orderOf b) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_iff_pow_eq_one.mpr hpow)
  have hc : (p : F) ≠ 0 := by
    intro hzero
    have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp hzero
    exact hp2 ((hp.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd)
  have hεid : IsIdempotentElem (fixIdem p b) := tbl_fixIdem_idem b hpow hc
  have hεadj : formAdj (RingHom.id F) (tblJ n F) (fixIdem p b) = fixIdem p b :=
    tbl_formAdj_fixIdem b hb hpow
  have hεA : fixIdem p b ∈ Algebra.adjoin F (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) F))) :=
    tbl_fixIdem_mem_adjoin p b
  have h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * fixIdem p b = fixIdem p b :=
    tbl_fixIdem_mul_left b hpow
  by_cases hε0 : fixIdem p b = 0
  · have hbot : trivBlock n F p s = ⊥ := by
      rw [trivBlock]
      apply le_antisymm _ bot_le
      intro x hx
      rw [Subgroup.mem_bot]
      have hfix : ((x : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (1 - fixIdem p b) =
          1 - fixIdem p b := (Subgroup.mem_comap.mp hx).2
      rw [hε0, sub_zero, Matrix.mul_one] at hfix
      exact Subtype.ext (Units.ext hfix)
    refine ⟨0, ?_, ?_, ?_, ?_⟩
    · rw [show fixIdem p (s : GL (Fin n ⊕ Fin n) F) = fixIdem p b from rfl, hε0,
        Matrix.rank_zero]
    · rw [hbot]
      haveI : Subsingleton ↥(StatedSp 0 F) := by
        constructor
        intro x y
        apply Subtype.ext
        apply Units.ext
        ext i j
        rcases i with i | i <;> exact i.elim0
      exact ⟨{
        toFun := fun _ => 1
        invFun := fun _ => 1
        left_inv := fun x => Subsingleton.elim _ _
        right_inv := fun x => Subsingleton.elim _ _
        map_mul' := fun x y => Subsingleton.elim _ _ }⟩
    · rw [hbot, Subgroup.bot_subgroupOf]
      exact Subgroup.normal_bot
    · intro g _
      refine ⟨1, ?_, ?_⟩
      · rw [hbot]
        exact Subgroup.mem_bot.mpr rfl
      · intro l hl
        rw [hbot] at hl
        rw [Subgroup.mem_bot.mp hl]
        group
  · have hεprim := tbl_fixIdem_prim b hpow hεid hε0
    have hIsPrim : IsPrimAdjIdemIn (RingHom.id F) (tblJ n F)
        (Algebra.adjoin F (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) F)))) (fixIdem p b) :=
      ⟨hεA, hεid, hε0, hεadj, hεprim⟩
    obtain ⟨m, hmrank, hmiso⟩ := blockGroup_iso_Sp_one b hb hodd hIsPrim h1
    refine ⟨m, ?_, ?_, ?_, ?_⟩
    · rw [show fixIdem p (s : GL (Fin n ⊕ Fin n) F) = fixIdem p b from rfl]
      rw [hmrank, tbl_rank_eq_finrank]
    · rw [trivBlock]
      exact hmiso
    · have hle : trivBlock n F p s ≤ Subgroup.centralizer ({s} : Set ↥(StatedSp n F)) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have hx' : (x : GL (Fin n ⊕ Fin n) F) ∈ (Subgroup.centralizer
            ({(b : GL (Fin n ⊕ Fin n) F)} : Set (GL (Fin n ⊕ Fin n) F)) ⊓
            glFixing (1 - fixIdem p b)) := by
          rw [trivBlock, glBlockCentralizer] at hx
          exact Subgroup.mem_comap.mp hx
        have hcomm := Subgroup.mem_centralizer_iff.mp hx'.1 b (Set.mem_singleton b)
        apply Subtype.ext
        simpa only [Subgroup.coe_mul, b] using hcomm
      refine (Subgroup.normal_subgroupOf_iff hle).mpr ?_
      intro h k hh hk
      have hhC : h ∈ Subgroup.centralizer ({s} : Set ↥(StatedSp n F)) := hle hh
      have hmemC : k * h * k⁻¹ ∈ Subgroup.centralizer ({s} : Set ↥(StatedSp n F)) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hhC) (Subgroup.inv_mem _ hk)
      have hk_comm : Commute (k : GL (Fin n ⊕ Fin n) F) b := by
        have hkc : (k : GL (Fin n ⊕ Fin n) F) ∈ Subgroup.centralizer
            ({(b : GL (Fin n ⊕ Fin n) F)} : Set (GL (Fin n ⊕ Fin n) F)) :=
          (tbl_coe_mem_centralizer_singleton s k).mpr hk
        exact (Subgroup.mem_centralizer_iff.mp hkc b (Set.mem_singleton b)).symm
      have hkε : ((k : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * fixIdem p b =
          fixIdem p b * ((k : GL (Fin n ⊕ Fin n) F) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
        tbl_fixIdem_comm_of_comm b (k : GL (Fin n ⊕ Fin n) F) hk_comm
      have hh' : (h : GL (Fin n ⊕ Fin n) F) ∈ (Subgroup.centralizer
          ({(b : GL (Fin n ⊕ Fin n) F)} : Set (GL (Fin n ⊕ Fin n) F)) ⊓
          glFixing (1 - fixIdem p b)) := by
        rw [trivBlock, glBlockCentralizer] at hh
        exact Subgroup.mem_comap.mp hh
      have hhfix : ((h : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (1 - fixIdem p b) =
          1 - fixIdem p b := hh'.2
      rw [trivBlock, glBlockCentralizer, Subgroup.mem_comap]
      refine ⟨?_, ?_⟩
      · exact (tbl_coe_mem_centralizer_singleton s (k * h * k⁻¹)).mpr hmemC
      · push_cast
        exact tbl_conj_fixes (k : GL (Fin n ⊕ Fin n) F) (h : GL (Fin n ⊕ Fin n) F) hkε hhfix
    · intro g hg
      have hg_comm : Commute (g : GL (Fin n ⊕ Fin n) F) b := by
        have := congrArg (fun x : ↥(StatedSp n F) => (x : GL (Fin n ⊕ Fin n) F)) hg
        show (g : GL (Fin n ⊕ Fin n) F) * b = b * (g : GL (Fin n ⊕ Fin n) F)
        simpa only [Subgroup.coe_mul, b] using this
      have hgε : ((g : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * fixIdem p b =
          fixIdem p b * ((g : GL (Fin n ⊕ Fin n) F) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
        tbl_fixIdem_comm_of_comm b (g : GL (Fin n ⊕ Fin n) F) hg_comm
      let R : GL (Fin n ⊕ Fin n) F :=
        tblBlk (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b) hεid hgε
      have hRsp : R ∈ StatedSp n F :=
        tbl_blk_mem_statedSp (g : GL (Fin n ⊕ Fin n) F) g.2 (fixIdem p b) hεid hgε hεadj
      let rSp : ↥(StatedSp n F) := ⟨R, hRsp⟩
      have hεb : fixIdem p b * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * fixIdem p b :=
        (tbl_fixIdem_comm_of_comm b b (Commute.refl b)).symm
      have hRcomm : tblBlkVal (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b) *
          (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            tblBlkVal (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b) :=
        tbl_blk_comm b (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b)
          (by simpa only [Units.val_mul] using congrArg Units.val hg_comm.eq) hεb
      have hrSp : rSp ∈ trivBlock n F p s := by
        rw [trivBlock, glBlockCentralizer, Subgroup.mem_comap]
        refine ⟨?_, ?_⟩
        · apply (tbl_coe_mem_centralizer_singleton s rSp).mpr
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          apply Subtype.ext
          apply Units.ext
          change (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
              ((rSp : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
            ((rSp : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
              (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          rw [show ((rSp : GL (Fin n ⊕ Fin n) F) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
              tblBlkVal (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b) from rfl]
          exact hRcomm.symm
        · change ((rSp : GL (Fin n ⊕ Fin n) F) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
              (1 - fixIdem p b) = 1 - fixIdem p b
          rw [show (rSp : GL (Fin n ⊕ Fin n) F) =
              tblBlkVal (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b) from rfl]
          exact tbl_blkVal_fixes (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b) hεid
      refine ⟨rSp, hrSp, ?_⟩
      intro l hl
      have hLfix : ((l : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (1 - fixIdem p b) =
          1 - fixIdem p b := by
        have hl' : (l : GL (Fin n ⊕ Fin n) F) ∈ (Subgroup.centralizer
            ({(b : GL (Fin n ⊕ Fin n) F)} : Set (GL (Fin n ⊕ Fin n) F)) ⊓
            glFixing (1 - fixIdem p b)) := by
          rw [trivBlock, glBlockCentralizer] at hl
          exact Subgroup.mem_comap.mp hl
        exact hl'.2
      have hl_comm : Commute (l : GL (Fin n ⊕ Fin n) F) b := by
        have hl' : (l : GL (Fin n ⊕ Fin n) F) ∈ Subgroup.centralizer
            ({(b : GL (Fin n ⊕ Fin n) F)} : Set (GL (Fin n ⊕ Fin n) F)) := by
          rw [trivBlock, glBlockCentralizer] at hl
          exact (Subgroup.mem_comap.mp hl).1
        exact (Subgroup.mem_centralizer_iff.mp hl' b (Set.mem_singleton b)).symm
      have hlε : ((l : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * fixIdem p b =
          fixIdem p b * ((l : GL (Fin n ⊕ Fin n) F) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
        tbl_fixIdem_comm_of_comm b (l : GL (Fin n ⊕ Fin n) F) hl_comm
      have hconjfix : (((g : GL (Fin n ⊕ Fin n) F)⁻¹ : GL (Fin n ⊕ Fin n) F) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          ((l : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          (1 - fixIdem p b) = 1 - fixIdem p b :=
        tbl_conj_fixes_inv (g : GL (Fin n ⊕ Fin n) F) (l : GL (Fin n ⊕ Fin n) F) hgε hLfix
      have hRHS : tblBlkInvVal (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b) *
            ((l : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            tblBlkVal (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b) =
          (((g : GL (Fin n ⊕ Fin n) F)⁻¹ : GL (Fin n ⊕ Fin n) F) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            ((l : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
        conv_lhs =>
          rw [tblBlkInvVal, tblBlkVal,
            show ((l : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
                ((l : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
                  fixIdem p b + (1 - fixIdem p b) from
              tbl_eq_blkVal (fixIdem p b) _ hLfix,
            tbl_blk_mul hεid hlε, tbl_blk_mul hεid hgε]
        rw [show ((((g : GL (Fin n ⊕ Fin n) F)⁻¹ : GL (Fin n ⊕ Fin n) F) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
              ((l : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) *
              ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
            (((g : GL (Fin n ⊕ Fin n) F)⁻¹ : GL (Fin n ⊕ Fin n) F) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
              ((l : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
              ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            from by noncomm_ring]
        exact (tbl_eq_blkVal (fixIdem p b) _ hconjfix).symm
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul]
      change (((g : GL (Fin n ⊕ Fin n) F)⁻¹ : GL (Fin n ⊕ Fin n) F) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            ((l : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          tblBlkInvVal (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b) *
            ((l : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            tblBlkVal (g : GL (Fin n ⊕ Fin n) F) (fixIdem p b)
      exact hRHS.symm

end CFSG.StandardType.TableC

end
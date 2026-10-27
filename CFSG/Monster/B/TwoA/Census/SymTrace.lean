module

public import Mathlib.LinearAlgebra.Trace

public noncomputable section

namespace CFSG.Monster.B.TwoA.Census

open Matrix

section Compl

variable {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]

theorem trace_eq_add_of_isCompl {p q : Submodule ℚ E} (h : IsCompl p q) (f : E →ₗ[ℚ] E)
    (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q) :
    LinearMap.trace ℚ E f =
      LinearMap.trace ℚ p (f.restrict hp) + LinearMap.trace ℚ q (f.restrict hq) := by
  set e := Submodule.prodEquivOfIsCompl p q h
  have hconj : e.symm.conj f = (f.restrict hp).prodMap (f.restrict hq) := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply e.injective
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, LinearMap.prodMap_apply]
    rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add]
    rfl
  rw [← LinearMap.trace_conj' f e.symm, hconj, LinearMap.trace_prodMap']

omit [FiniteDimensional ℚ E] in
theorem trace_mapQ_of_isCompl {p q : Submodule ℚ E} (h : IsCompl p q) (f : E →ₗ[ℚ] E)
    (hp : p ≤ p.comap f) (hq : ∀ x ∈ q, f x ∈ q) :
    LinearMap.trace ℚ (E ⧸ p) (p.mapQ p f hp) = LinearMap.trace ℚ q (f.restrict hq) := by
  set e := Submodule.quotientEquivOfIsCompl p q h
  have hconj : e.conj (p.mapQ p f hp) = f.restrict hq := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, Submodule.quotientEquivOfIsCompl_symm_apply,
      Submodule.mapQ_apply]
    have : (f x : E) = ((f.restrict hq x : q) : E) := rfl
    rw [this, Submodule.quotientEquivOfIsCompl_apply_mk_right]
  rw [← LinearMap.trace_conj' _ e, hconj]

omit [FiniteDimensional ℚ E] in
theorem trace_restrict_span_singleton {v : E} (hv : v ≠ 0) (f : E →ₗ[ℚ] E) (hf : f v = v)
    (hp : ∀ x ∈ (ℚ ∙ v), f x ∈ (ℚ ∙ v)) :
    LinearMap.trace ℚ (ℚ ∙ v) (f.restrict hp) = 1 := by
  have hid : f.restrict hp = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.coe_restrict_apply, map_smul, hf, LinearMap.id_apply]
  rw [hid, LinearMap.trace_id, finrank_span_singleton hv, Nat.cast_one]

end Compl

variable {n : Type*} [Fintype n]

@[expose] def symSub (n : Type*) [Fintype n] : Submodule ℚ (Matrix n n ℚ) where
  carrier := {S | Sᵀ = S}
  add_mem' {a b} ha hb := by
    change (a + b)ᵀ = a + b
    rw [transpose_add, show aᵀ = a from ha, show bᵀ = b from hb]
  zero_mem' := transpose_zero
  smul_mem' c S hS := by
    change (c • S)ᵀ = c • S
    rw [transpose_smul, show Sᵀ = S from hS]

@[expose] def altSub (n : Type*) [Fintype n] : Submodule ℚ (Matrix n n ℚ) where
  carrier := {S | Sᵀ = -S}
  add_mem' {a b} ha hb := by
    change (a + b)ᵀ = -(a + b)
    rw [transpose_add, show aᵀ = -a from ha, show bᵀ = -b from hb, neg_add]
  zero_mem' := by
    change (0 : Matrix n n ℚ)ᵀ = -0
    rw [transpose_zero, neg_zero]
  smul_mem' c S hS := by
    change (c • S)ᵀ = -(c • S)
    rw [transpose_smul, show Sᵀ = -S from hS, smul_neg]

theorem mem_symSub {S : Matrix n n ℚ} : S ∈ symSub n ↔ Sᵀ = S := Iff.rfl

theorem mem_altSub {S : Matrix n n ℚ} : S ∈ altSub n ↔ Sᵀ = -S := Iff.rfl

theorem isCompl_sym_alt : IsCompl (symSub n) (altSub n) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hs ha
    rw [mem_symSub] at hs
    rw [mem_altSub, hs] at ha
    have : (2 : ℚ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [ha]; exact neg_add_cancel x
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (1 / 2 : ℚ) • (x + xᵀ) + (1 / 2 : ℚ) • (x - xᵀ) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul ℚ x, smul_smul]
      norm_num
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mem_symSub, transpose_smul, transpose_add, transpose_transpose, add_comm]
    · rw [mem_altSub, transpose_smul, transpose_sub, transpose_transpose, ← smul_neg, neg_sub]

@[expose] def conjM (g : Matrix n n ℚ) : Matrix n n ℚ →ₗ[ℚ] Matrix n n ℚ where
  toFun X := g * X * gᵀ
  map_add' X Y := by rw [mul_add, add_mul]
  map_smul' c X := by rw [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

@[expose] def conjMT (g : Matrix n n ℚ) : Matrix n n ℚ →ₗ[ℚ] Matrix n n ℚ :=
  (conjM g).comp (transposeLinearEquiv n n ℚ ℚ).toLinearMap

theorem conjM_apply (g X : Matrix n n ℚ) : conjM g X = g * X * gᵀ := rfl

theorem conjMT_apply (g X : Matrix n n ℚ) : conjMT g X = g * Xᵀ * gᵀ := rfl

theorem conjM_sym (g : Matrix n n ℚ) : ∀ X ∈ symSub n, conjM g X ∈ symSub n := by
  intro X hX
  rw [mem_symSub, conjM_apply, transpose_mul, transpose_mul, transpose_transpose,
    show Xᵀ = X from hX, mul_assoc]

theorem conjM_alt (g : Matrix n n ℚ) : ∀ X ∈ altSub n, conjM g X ∈ altSub n := by
  intro X hX
  rw [mem_altSub, conjM_apply, transpose_mul, transpose_mul, transpose_transpose,
    show Xᵀ = -X from hX, mul_assoc, Matrix.neg_mul, Matrix.mul_neg]

theorem conjMT_sym (g : Matrix n n ℚ) : ∀ X ∈ symSub n, conjMT g X ∈ symSub n := by
  intro X hX
  rw [conjMT_apply, show Xᵀ = X from hX]
  exact conjM_sym g X hX

theorem conjMT_alt (g : Matrix n n ℚ) : ∀ X ∈ altSub n, conjMT g X ∈ altSub n := by
  intro X hX
  rw [conjMT_apply, show Xᵀ = -X from hX, Matrix.mul_neg, Matrix.neg_mul]
  exact (altSub n).neg_mem (conjM_alt g X hX)

@[expose] def symConj (g : Matrix n n ℚ) : symSub n →ₗ[ℚ] symSub n :=
  (conjM g).restrict (conjM_sym g)

theorem coe_symConj (g : Matrix n n ℚ) (S : symSub n) :
    (symConj g S : Matrix n n ℚ) = g * S * gᵀ := rfl

variable [DecidableEq n]

@[expose] def pairEquiv (n : Type*) [Fintype n] : Matrix n n ℚ ≃ₗ[ℚ] (n × n → ℚ) :=
  (LinearEquiv.curry ℚ ℚ n n).symm

omit [DecidableEq n] in
theorem pairEquiv_apply (X : Matrix n n ℚ) (p : n × n) : pairEquiv n X p = X p.1 p.2 := rfl

theorem pairEquiv_symm_single (p : n × n) :
    (pairEquiv n).symm (Pi.single p 1) = Matrix.single p.1 p.2 (1 : ℚ) := by
  ext i j
  rw [Matrix.single_apply]
  change (Pi.single p (1 : ℚ) : n × n → ℚ) (i, j) = _
  rw [Pi.single_apply]
  by_cases h : (i, j) = p
  · subst h
    simp
  · have h' : ¬(p.1 = i ∧ p.2 = j) := by
      rintro ⟨rfl, rfl⟩
      exact h rfl
    simp [h, h']

theorem trace_eq_sum_pairs (f : Matrix n n ℚ →ₗ[ℚ] Matrix n n ℚ) :
    LinearMap.trace ℚ _ f = ∑ p : n × n, f (Matrix.single p.1 p.2 1) p.1 p.2 := by
  rw [← LinearMap.trace_conj' f (pairEquiv n), LinearMap.trace_eq_matrix_trace ℚ
    (Pi.basisFun ℚ (n × n)), LinearMap.toMatrix_eq_toMatrix', Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix'_apply, LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, pairEquiv_symm_single,
    pairEquiv_apply]

theorem mul_single_mul_apply (g : Matrix n n ℚ) (i j a b : n) :
    (g * Matrix.single i j (1 : ℚ) * gᵀ) a b = g a i * g b j := by
  have h1 : ∀ k, (g * Matrix.single i j (1 : ℚ)) a k = if j = k then g a i else 0 := by
    intro k
    rw [Matrix.mul_apply]
    simp only [Matrix.single_apply]
    by_cases hk : j = k
    · simp [hk]
    · simp [hk]
  rw [Matrix.mul_apply]
  simp only [h1, Matrix.transpose_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

theorem trace_conjM (g : Matrix n n ℚ) : LinearMap.trace ℚ _ (conjM g) = (trace g) ^ 2 := by
  rw [trace_eq_sum_pairs, Fintype.sum_prod_type, sq, Matrix.trace, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [conjM_apply, mul_single_mul_apply, Matrix.diag_apply, Matrix.diag_apply]

theorem trace_conjMT (g : Matrix n n ℚ) : LinearMap.trace ℚ _ (conjMT g) = trace (g * g) := by
  rw [trace_eq_sum_pairs, Fintype.sum_prod_type, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjMT_apply, Matrix.transpose_single, mul_single_mul_apply]

theorem trace_symConj (g : Matrix n n ℚ) :
    LinearMap.trace ℚ _ (symConj g) = ((trace g) ^ 2 + trace (g * g)) / 2 := by
  have h1 := trace_eq_add_of_isCompl isCompl_sym_alt (conjM g) (conjM_sym g) (conjM_alt g)
  have h2 := trace_eq_add_of_isCompl isCompl_sym_alt (conjMT g) (conjMT_sym g) (conjMT_alt g)
  have e1 : (conjMT g).restrict (conjMT_sym g) = (conjM g).restrict (conjM_sym g) := by
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    change g * (X : Matrix n n ℚ)ᵀ * gᵀ = g * X * gᵀ
    rw [show (X : Matrix n n ℚ)ᵀ = X from X.2]
  have e2 : (conjMT g).restrict (conjMT_alt g) = (-1 : ℚ) • (conjM g).restrict (conjM_alt g) := by
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    change g * (X : Matrix n n ℚ)ᵀ * gᵀ = (-1 : ℚ) • (g * X * gᵀ)
    rw [show (X : Matrix n n ℚ)ᵀ = -X from X.2, Matrix.mul_neg, Matrix.neg_mul, neg_one_smul]
  rw [e1, e2, map_smul, smul_eq_mul, trace_conjMT] at h2
  rw [trace_conjM] at h1
  rw [symConj]
  linarith

@[expose] def symOne : symSub n := ⟨1, transpose_one⟩

@[expose] def scalarLine : Submodule ℚ (symSub n) := ℚ ∙ (symOne : symSub n)

@[expose] def symTr : symSub n →ₗ[ℚ] ℚ := (Matrix.traceLinearMap n ℚ ℚ).comp (symSub n).subtype

@[expose] def traceless : Submodule ℚ (symSub n) := LinearMap.ker (symTr (n := n))

theorem symTr_symOne [Nonempty n] : symTr (symOne : symSub n) ≠ 0 := by
  change Matrix.trace (1 : Matrix n n ℚ) ≠ 0
  rw [Matrix.trace_one]
  exact_mod_cast Fintype.card_ne_zero

theorem isCompl_scalarLine [Nonempty n] :
    IsCompl (scalarLine : Submodule ℚ (symSub n)) traceless := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [traceless, LinearMap.mem_ker, map_smul, smul_eq_mul] at hx'
    rcases mul_eq_zero.1 hx' with h | h
    · rw [h, zero_smul]
    · exact absurd h symTr_symOne
  · rw [codisjoint_iff]
    exact LinearMap.span_singleton_sup_ker_eq_top symTr symTr_symOne

variable {g : Matrix n n ℚ}

theorem symConj_symOne (hg : g * gᵀ = 1) : symConj g symOne = symOne :=
  Subtype.ext (by
    change g * 1 * gᵀ = 1
    rw [Matrix.mul_one, hg])

theorem scalarLine_le_comap (hg : g * gᵀ = 1) :
    (scalarLine : Submodule ℚ (symSub n)) ≤ scalarLine.comap (symConj g) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [Submodule.mem_comap, map_smul, symConj_symOne hg]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

theorem symConj_traceless (hg : g * gᵀ = 1) :
    ∀ x ∈ (traceless : Submodule ℚ (symSub n)), symConj g x ∈ traceless := by
  intro x hx
  rw [traceless, LinearMap.mem_ker] at hx ⊢
  change Matrix.trace (g * (x : Matrix n n ℚ) * gᵀ) = 0
  rw [Matrix.trace_mul_cycle, mul_eq_one_comm.1 hg, Matrix.one_mul]
  exact hx

@[expose] def symQuotConj (g : Matrix n n ℚ) (hg : g * gᵀ = 1) :
    (symSub n ⧸ (scalarLine : Submodule ℚ (symSub n))) →ₗ[ℚ]
      (symSub n ⧸ (scalarLine : Submodule ℚ (symSub n))) :=
  scalarLine.mapQ scalarLine (symConj g) (scalarLine_le_comap hg)

theorem trace_symQuotConj [Nonempty n] (hg : g * gᵀ = 1) :
    LinearMap.trace ℚ _ (symQuotConj g hg) = ((trace g) ^ 2 + trace (g * g)) / 2 - 1 := by
  have hp : ∀ x ∈ (scalarLine : Submodule ℚ (symSub n)), symConj g x ∈ scalarLine :=
    fun x hx => scalarLine_le_comap hg hx
  have h1 := trace_eq_add_of_isCompl isCompl_scalarLine (symConj g) hp (symConj_traceless hg)
  have h2 := trace_mapQ_of_isCompl isCompl_scalarLine (symConj g) (scalarLine_le_comap hg)
    (symConj_traceless hg)
  have hone : LinearMap.trace ℚ (scalarLine : Submodule ℚ (symSub n))
      ((symConj g).restrict hp) = 1 :=
    trace_restrict_span_singleton (fun h => symTr_symOne (by rw [h, map_zero])) (symConj g)
      (symConj_symOne hg) hp
  rw [symQuotConj, h2, ← trace_symConj g]
  linarith

end CFSG.Monster.B.TwoA.Census

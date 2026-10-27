module

public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Tables

open Matrix
open scoped commutatorElement MatrixGroups

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] def IsBlockDiag {α : Type*} (t : ι → α) (M : Matrix ι ι K) : Prop :=
  ∀ i j, t i ≠ t j → M i j = 0

theorem isBlockDiag_of_commute {t : ι → K} {M : Matrix ι ι K}
    (h : M * diagonal t = diagonal t * M) : IsBlockDiag t M := by
  intro i j hij
  have e := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at e
  have e' : (t j - t i) * M i j = 0 := by linear_combination e
  rcases mul_eq_zero.mp e' with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hij
  · exact h0

theorem commute_of_isBlockDiag {t : ι → K} {M : Matrix ι ι K} (h : IsBlockDiag t M) :
    M * diagonal t = diagonal t * M := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hij : t i = t j
  · rw [hij, mul_comm]
  · rw [h i j hij, zero_mul, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem IsBlockDiag.of_comp {α β : Type*} {t : ι → α} {f : α → β} (hf : Function.Injective f)
    {M : Matrix ι ι K} (h : IsBlockDiag (f ∘ t) M) : IsBlockDiag t M :=
  fun i j hij => h i j fun e => hij (hf e)

omit [Fintype ι] [DecidableEq ι] in
theorem IsBlockDiag.comp {α β : Type*} {t : ι → α} (f : α → β) {M : Matrix ι ι K}
    (h : IsBlockDiag t M) : IsBlockDiag (f ∘ t) M :=
  fun i j hij => h i j fun e => hij (by simp [e])

theorem commute_diagonal_of_isBlockDiag {α : Type*} {t : ι → α} {s : ι → K}
    (hs : ∀ i j, t i = t j → s i = s j) {M : Matrix ι ι K} (hM : IsBlockDiag t M) :
    M * diagonal s = diagonal s * M := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hij : t i = t j
  · rw [hs i j hij, mul_comm]
  · rw [hM i j hij, zero_mul, mul_zero]

@[expose] def IsIdOutside (c : Set ι) (M : Matrix ι ι K) : Prop :=
  ∀ i j, (i ∉ c ∨ j ∉ c) → M i j = (1 : Matrix ι ι K) i j

theorem IsIdOutside.mul {c : Set ι} {M N : Matrix ι ι K} (hM : IsIdOutside c M)
    (hN : IsIdOutside c N) : IsIdOutside c (M * N) := by
  intro i j hij
  rcases hij with hi | hj
  · have hrow : ∀ k, M i k = (1 : Matrix ι ι K) i k := fun k => hM i k (Or.inl hi)
    rw [Matrix.mul_apply]
    simp_rw [hrow, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [← Matrix.one_apply]
    exact hN i j (Or.inl hi)
  · have hcol : ∀ k, N k j = (1 : Matrix ι ι K) k j := fun k => hN k j (Or.inr hj)
    rw [Matrix.mul_apply]
    simp_rw [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [← Matrix.one_apply]
    exact hM i j (Or.inr hj)

omit [Fintype ι] in
theorem isIdOutside_diagonal {c : Set ι} {d : ι → K} (hd : ∀ i, i ∉ c → d i = 1) :
    IsIdOutside c (diagonal d) := by
  intro i j hij
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq, Matrix.one_apply_eq]
    rcases hij with hi | hi <;> exact hd i hi
  · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h]

omit [Fintype ι] in
theorem IsIdOutside.isBlockDiag {α : Type*} {t : ι → α} {κ : α} {M : Matrix ι ι K}
    (h : IsIdOutside {i | t i = κ} M) : IsBlockDiag t M := by
  intro i j hij
  have hne : i ≠ j := fun e => hij (e ▸ rfl)
  have hout : i ∉ {i | t i = κ} ∨ j ∉ {i | t i = κ} := by
    by_contra hc
    push Not at hc
    exact hij (hc.1.trans hc.2.symm)
  rw [h i j hout, Matrix.one_apply_ne hne]

theorem IsIdOutside.conj_of_union {α : Type*} {t : ι → α} {c : Set ι}
    (hc : ∀ i j, t i = t j → (i ∈ c ↔ j ∈ c)) {g g' S : Matrix ι ι K}
    (hg : IsBlockDiag t g) (hg' : IsBlockDiag t g') (hgg' : g * g' = 1)
    (hS : IsIdOutside c S) : IsIdOutside c (g * S * g') := by
  set N := S - 1
  have hSN : S = 1 + N := by rw [add_sub_cancel]
  have hN : ∀ k l, (k ∉ c ∨ l ∉ c) → N k l = 0 := by
    intro k l hkl
    change (S - 1) k l = 0
    rw [Matrix.sub_apply, hS k l hkl, sub_self]
  have key : ∀ i j, (i ∉ c ∨ j ∉ c) → (g * N * g') i j = 0 := by
    intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ c
    · by_cases hl : l ∈ c
      · rcases hij with hi | hj
        · have : t i ≠ t k := fun e => hi ((hc i k e).mpr hk)
          rw [hg i k this, zero_mul, zero_mul]
        · have : t l ≠ t j := fun e => hj ((hc l j e).mp hl)
          rw [hg' l j this, mul_zero]
      · rw [hN k l (Or.inr hl), mul_zero, zero_mul]
    · rw [hN k l (Or.inl hk), mul_zero, zero_mul]
  intro i j hij
  rw [hSN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg', Matrix.add_apply, key i j hij,
    add_zero]

theorem IsIdOutside.conj {α : Type*} {t : ι → α} {κ : α} {g g' S : Matrix ι ι K}
    (hg : IsBlockDiag t g) (hg' : IsBlockDiag t g') (hgg' : g * g' = 1)
    (hS : IsIdOutside {i | t i = κ} S) : IsIdOutside {i | t i = κ} (g * S * g') :=
  IsIdOutside.conj_of_union (fun i j e => by simp only [Set.mem_ofPred_eq, e]) hg hg' hgg' hS

@[expose] def reindexSL (σ : Equiv.Perm ι) :
    SpecialLinearGroup ι K ≃* SpecialLinearGroup ι K where
  toFun g := ⟨(g : Matrix ι ι K).submatrix σ σ, by rw [det_submatrix_equiv_self]; exact g.2⟩
  invFun g := ⟨(g : Matrix ι ι K).submatrix σ.symm σ.symm,
    by rw [det_submatrix_equiv_self]; exact g.2⟩
  left_inv g := by
    apply Subtype.ext
    ext i j
    simp
  right_inv g := by
    apply Subtype.ext
    ext i j
    simp
  map_mul' g h := by
    apply Subtype.ext
    change ((g : Matrix ι ι K) * (h : Matrix ι ι K)).submatrix σ σ =
      (g : Matrix ι ι K).submatrix σ σ * (h : Matrix ι ι K).submatrix σ σ
    exact (submatrix_mul_equiv _ _ _ _ _).symm

theorem coe_reindexSL (σ : Equiv.Perm ι) (g : SpecialLinearGroup ι K) :
    ((reindexSL σ g : SpecialLinearGroup ι K) : Matrix ι ι K) =
      (g : Matrix ι ι K).submatrix σ σ := rfl


@[expose] def reindexGL (σ : Equiv.Perm ι) : GL ι K ≃* GL ι K where
  toFun g := ⟨(g : Matrix ι ι K).submatrix σ σ, ((g⁻¹ : GL ι K) : Matrix ι ι K).submatrix σ σ,
    by rw [submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv],
    by rw [submatrix_mul_equiv, Units.inv_mul, submatrix_one_equiv]⟩
  invFun g := ⟨(g : Matrix ι ι K).submatrix σ.symm σ.symm,
    ((g⁻¹ : GL ι K) : Matrix ι ι K).submatrix σ.symm σ.symm,
    by rw [submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv],
    by rw [submatrix_mul_equiv, Units.inv_mul, submatrix_one_equiv]⟩
  left_inv g := Units.ext (by ext i j; simp)
  right_inv g := Units.ext (by ext i j; simp)
  map_mul' g h := Units.ext (by
    change ((g : Matrix ι ι K) * (h : Matrix ι ι K)).submatrix σ σ =
      (g : Matrix ι ι K).submatrix σ σ * (h : Matrix ι ι K).submatrix σ σ
    exact (submatrix_mul_equiv _ _ _ _ _).symm)

theorem coe_reindexGL (σ : Equiv.Perm ι) (g : GL ι K) :
    ((reindexGL σ g : GL ι K) : Matrix ι ι K) = (g : Matrix ι ι K).submatrix σ σ := rfl

theorem isQuasisimple_of_isSimpleGroup {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ x y : X, x * y ≠ y * x) : CFSG.IsQuasisimple X := by
  have := hs
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have hx : x ∈ Subgroup.center X := h ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
  have hperf : Group.IsPerfect X := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have : ⁅x, y⁆ ∈ commutator X := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
        (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact ⟨h⟩
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := hnc
  exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩

end CFSG.RankThree.PartTwo.Sec21.Tables

module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.RankThree.PartOne.KFCL.BlockSL

open Matrix

variable {K : Type*} [Field K]

section Split

variable {m : Type*} [Fintype m] [DecidableEq m] (p : m → Prop) [DecidablePred p]

@[expose] def ext1 (A : Matrix {i // p i} {i // p i} K) : Matrix m m K :=
  Matrix.reindex (Equiv.sumCompl p) (Equiv.sumCompl p) (Matrix.fromBlocks A 0 0 1)

@[expose] def ext2 (B : Matrix {i // ¬ p i} {i // ¬ p i} K) : Matrix m m K :=
  Matrix.reindex (Equiv.sumCompl p) (Equiv.sumCompl p) (Matrix.fromBlocks 1 0 0 B)

theorem ext1_mul (A B : Matrix {i // p i} {i // p i} K) : ext1 p (A * B) = ext1 p A * ext1 p B := by
  unfold ext1
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem ext2_mul (A B : Matrix {i // ¬ p i} {i // ¬ p i} K) :
    ext2 p (A * B) = ext2 p A * ext2 p B := by
  unfold ext2
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

omit [Fintype m] in
theorem ext1_one : ext1 p (1 : Matrix {i // p i} {i // p i} K) = 1 := by
  unfold ext1
  simp

omit [Fintype m] in
theorem ext2_one : ext2 p (1 : Matrix {i // ¬ p i} {i // ¬ p i} K) = 1 := by
  unfold ext2
  simp

theorem ext1_det (A : Matrix {i // p i} {i // p i} K) : (ext1 p A).det = A.det := by
  unfold ext1
  rw [Matrix.reindex_apply, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem ext2_det (B : Matrix {i // ¬ p i} {i // ¬ p i} K) : (ext2 p B).det = B.det := by
  unfold ext2
  rw [Matrix.reindex_apply, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem ext1_mul_ext2 (A : Matrix {i // p i} {i // p i} K) (B : Matrix {i // ¬ p i} {i // ¬ p i} K) :
    ext1 p A * ext2 p B =
      Matrix.reindex (Equiv.sumCompl p) (Equiv.sumCompl p) (Matrix.fromBlocks A 0 0 B) := by
  unfold ext1 ext2
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem ext2_mul_ext1 (A : Matrix {i // p i} {i // p i} K) (B : Matrix {i // ¬ p i} {i // ¬ p i} K) :
    ext2 p B * ext1 p A =
      Matrix.reindex (Equiv.sumCompl p) (Equiv.sumCompl p) (Matrix.fromBlocks A 0 0 B) := by
  unfold ext1 ext2
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

@[expose] def blk1 (M : Matrix m m K) : Matrix {i // p i} {i // p i} K :=
  M.submatrix (Subtype.val : {i // p i} → m) Subtype.val

@[expose] def blk2 (M : Matrix m m K) : Matrix {i // ¬ p i} {i // ¬ p i} K :=
  M.submatrix (Subtype.val : {i // ¬ p i} → m) Subtype.val

theorem eq_ext1_mul_ext2 (M : Matrix m m K) (h12 : ∀ a b, p a → ¬ p b → M a b = 0)
    (h21 : ∀ a b, ¬ p a → p b → M a b = 0) : M = ext1 p (blk1 p M) * ext2 p (blk2 p M) := by
  rw [ext1_mul_ext2]
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  obtain ⟨a | a, rfl⟩ := (Equiv.sumCompl p).surjective i <;>
    obtain ⟨b | b, rfl⟩ := (Equiv.sumCompl p).surjective j
  · simp [blk1]
  · simp [h12 _ _ a.2 b.2]
  · simp [h21 _ _ a.2 b.2]
  · simp [blk2]

omit [DecidableEq m] in
theorem blk1_mul (M N : Matrix m m K) (h12 : ∀ a b, p a → ¬ p b → M a b = 0) :
    blk1 p (M * N) = blk1 p M * blk1 p N := by
  ext a b
  simp only [blk1, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← (Equiv.sumCompl p).sum_comp, Fintype.sum_sum_type]
  simp only [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
  have : ∑ k : {i // ¬ p i}, M a k * N k b = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [h12 a k a.2 k.2, zero_mul]
  rw [this, add_zero]

omit [DecidableEq m] in
theorem blk2_mul (M N : Matrix m m K) (h21 : ∀ a b, ¬ p a → p b → M a b = 0) :
    blk2 p (M * N) = blk2 p M * blk2 p N := by
  ext a b
  simp only [blk2, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← (Equiv.sumCompl p).sum_comp, Fintype.sum_sum_type]
  simp only [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
  have : ∑ k : {i // p i}, M a k * N k b = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [h21 a k a.2 k.2, zero_mul]
  rw [this, zero_add]

omit [Fintype m] in
theorem ext1_apply (A : Matrix {i // p i} {i // p i} K) (i j : m) :
    ext1 p A i j = if h : p i ∧ p j then A ⟨i, h.1⟩ ⟨j, h.2⟩ else (1 : Matrix m m K) i j := by
  unfold ext1
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hi : p i <;> by_cases hj : p j
  · simp [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_pos hj, hi, hj]
  · have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_neg hj, hi, hj, hij]
  · have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_pos hj, hi, hj, hij]
  · simp [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_neg hj, hi, hj,
      Matrix.one_apply, Subtype.ext_iff]

omit [Fintype m] in
theorem ext2_apply (B : Matrix {i // ¬ p i} {i // ¬ p i} K) (i j : m) :
    ext2 p B i j = if h : ¬ p i ∧ ¬ p j then B ⟨i, h.1⟩ ⟨j, h.2⟩ else (1 : Matrix m m K) i j := by
  unfold ext2
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hi : p i <;> by_cases hj : p j
  · simp [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_pos hj, hi, hj,
      Matrix.one_apply, Subtype.ext_iff]
  · have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_neg hj, hi, hj, hij]
  · have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_pos hj, hi, hj, hij]
  · simp [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_neg hj, hi, hj]

@[expose] def extHom1 : SpecialLinearGroup {i // p i} K →* SpecialLinearGroup m K where
  toFun A := ⟨ext1 p A.1, by rw [ext1_det]; exact A.2⟩
  map_one' := Subtype.ext (by simp [ext1_one])
  map_mul' A B := Subtype.ext (by simp only [SpecialLinearGroup.coe_mul]; exact ext1_mul p _ _)

theorem extHom1_coe (A : SpecialLinearGroup {i // p i} K) : (extHom1 p A).1 = ext1 p A.1 := rfl

@[expose] def extHom2 : SpecialLinearGroup {i // ¬ p i} K →* SpecialLinearGroup m K where
  toFun A := ⟨ext2 p A.1, by rw [ext2_det]; exact A.2⟩
  map_one' := Subtype.ext (by simp [ext2_one])
  map_mul' A B := Subtype.ext (by simp only [SpecialLinearGroup.coe_mul]; exact ext2_mul p _ _)

theorem extHom2_coe (A : SpecialLinearGroup {i // ¬ p i} K) : (extHom2 p A).1 = ext2 p A.1 := rfl

theorem extHom1_transvection {a b : {i // p i}} (hab : a ≠ b) (c : K) :
    extHom1 p (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection (fun h => hab (Subtype.ext h) : (a : m) ≠ b) c := by
  apply Subtype.ext
  ext i j
  rw [extHom1_coe]
  simp only [SpecialLinearGroup.transvection_coe, ext1_apply]
  by_cases hi : p i ∧ p j
  · rw [dite_eq_left hi]
    simp [Matrix.one_apply, Matrix.single_apply, Subtype.ext_iff]
  · rw [dite_eq_right hi]
    have : ¬ ((a : m) = i ∧ (b : m) = j) := fun ⟨h1, h2⟩ => hi ⟨h1 ▸ a.2, h2 ▸ b.2⟩
    simp [this]

theorem extHom2_transvection {a b : {i // ¬ p i}} (hab : a ≠ b) (c : K) :
    extHom2 p (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection (fun h => hab (Subtype.ext h) : (a : m) ≠ b) c := by
  apply Subtype.ext
  ext i j
  rw [extHom2_coe]
  simp only [SpecialLinearGroup.transvection_coe, ext2_apply]
  by_cases hi : ¬ p i ∧ ¬ p j
  · rw [dite_eq_left hi]
    simp [Matrix.one_apply, Matrix.single_apply, Subtype.ext_iff]
  · rw [dite_eq_right hi]
    have : ¬ ((a : m) = i ∧ (b : m) = j) := fun ⟨h1, h2⟩ => hi ⟨h1 ▸ a.2, h2 ▸ b.2⟩
    simp [this]

theorem mem_range_extHom1_iff (g : SpecialLinearGroup m K) :
    g ∈ (extHom1 (K := K) p).range ↔
      ∀ a b : m, ¬ (p a ∧ p b) → g.1 a b = (1 : Matrix m m K) a b := by
  constructor
  · rintro ⟨A, rfl⟩ a b hab
    rw [extHom1_coe, ext1_apply, dite_eq_right hab]
  · intro h
    have h12 : ∀ a b, p a → ¬ p b → g.1 a b = 0 := by
      intro a b ha hb
      rw [h a b (fun hh => hb hh.2)]
      exact Matrix.one_apply_ne (fun hab => hb (hab ▸ ha))
    have h21 : ∀ a b, ¬ p a → p b → g.1 a b = 0 := by
      intro a b ha hb
      rw [h a b (fun hh => ha hh.1)]
      exact Matrix.one_apply_ne (fun hab => ha (hab ▸ hb))
    have hsplit := eq_ext1_mul_ext2 p g.1 h12 h21
    have hb2 : blk2 p g.1 = 1 := by
      ext a b
      rw [blk2, Matrix.submatrix_apply, h a.1 b.1 (fun hh => a.2 hh.1)]
      simp [Matrix.one_apply, Subtype.ext_iff]
    rw [hb2, ext2_one, Matrix.mul_one] at hsplit
    have hdet : (blk1 p g.1).det = 1 := by
      have h1 := ext1_det p (blk1 p g.1)
      rw [← hsplit] at h1
      rw [← h1]
      exact g.2
    exact ⟨⟨blk1 p g.1, hdet⟩, Subtype.ext ((extHom1_coe p ⟨blk1 p g.1, hdet⟩).trans hsplit.symm)⟩

omit [Fintype m] in
theorem ext1_injective : Function.Injective (ext1 (K := K) p) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i.1) j.1
  rw [ext1_apply, ext1_apply, dite_eq_left (And.intro i.2 j.2), dite_eq_left (And.intro i.2 j.2)] at this
  exact this

theorem extHom1_injective : Function.Injective (extHom1 (K := K) p) :=
  fun _ _ h => Subtype.ext (ext1_injective p (congrArg Subtype.val h))

end Split

@[expose] def reindexSL {κ ℓ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ℓ] [DecidableEq ℓ] (e : κ ≃ ℓ) :
    SpecialLinearGroup κ K ≃* SpecialLinearGroup ℓ K where
  toFun A := ⟨Matrix.reindex e e A.1, by rw [Matrix.det_reindex_self]; exact A.2⟩
  invFun A := ⟨Matrix.reindex e.symm e.symm A.1, by rw [Matrix.det_reindex_self]; exact A.2⟩
  left_inv A := Subtype.ext (by ext i j; simp [Matrix.reindex_apply])
  right_inv A := Subtype.ext (by ext i j; simp [Matrix.reindex_apply])
  map_mul' A B := Subtype.ext (by
    show Matrix.reindex e e (A.1 * B.1) = Matrix.reindex e e A.1 * Matrix.reindex e e B.1
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv])


section Main

variable {m : Type*} [Fintype m] [DecidableEq m]

@[expose] def elemSet {κ : Type*} (cls : m → κ) : Set (SpecialLinearGroup m K) :=
  {g | ∃ (i j : m) (hij : i ≠ j) (a : K), cls i = cls j ∧ g = SpecialLinearGroup.transvection hij a}

theorem bd_mem_closure_aux : ∀ (n : ℕ) (m : Type) [Fintype m] [DecidableEq m], Fintype.card m = n →
    ∀ {κ : Type} [DecidableEq κ] (cls : m → κ) (g : SpecialLinearGroup m K),
      (∀ i j, cls i ≠ cls j → g.1 i j = 0) →
      (∀ k : κ, (g.1.submatrix (Subtype.val : {i // cls i = k} → m) Subtype.val).det = 1) →
      g ∈ Subgroup.closure (elemSet cls) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro m _ _ hn κ _ cls g hbd hdet
  classical
  rcases isEmpty_or_nonempty m with hm | ⟨⟨i₀⟩⟩
  · have : g = 1 := Subtype.ext (Subsingleton.elim _ _)
    rw [this]
    exact Subgroup.one_mem _
  · set κ₀ := cls i₀ with hκ₀
    let p : m → Prop := fun i => cls i = κ₀
    by_cases hall : ∀ i, p i
    · have hcls : ∀ i j, cls i = cls j := fun i j => (hall i).trans (hall j).symm
      have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
          Matrix.TransvectionStruct m K → SpecialLinearGroup m K)) ≤
          Subgroup.closure (elemSet cls) := by
        refine Subgroup.closure_mono ?_
        rintro _ ⟨t, rfl⟩
        exact ⟨t.i, t.j, t.hij, t.c, hcls _ _, rfl⟩
      rw [SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field] at hle
      exact hle (Subgroup.mem_top g)
    · push Not at hall
      have hcard : Fintype.card {i // ¬ p i} < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (p := fun i => ¬ p i) (x := i₀) (by simp [p, hκ₀])
      have h12 : ∀ a b, p a → ¬ p b → g.1 a b = 0 := fun a b ha hb =>
        hbd a b (fun h => hb (h.symm.trans ha))
      have h21 : ∀ a b, ¬ p a → p b → g.1 a b = 0 := fun a b ha hb =>
        hbd a b (fun h => ha (h.trans hb))
      have hsplit := eq_ext1_mul_ext2 p g.1 h12 h21
      have hdetA : (blk1 p g.1).det = 1 := hdet κ₀
      have hdetg : g.1.det = 1 := g.2
      have hdetB : (blk2 p g.1).det = 1 := by
        have h1 : g.1.det = (blk1 p g.1).det * (blk2 p g.1).det := by
          conv_lhs => rw [hsplit]
          rw [Matrix.det_mul, ext1_det, ext2_det]
        rw [hdetA, one_mul] at h1
        rw [← h1, hdetg]
      let A' : SpecialLinearGroup {i // p i} K := ⟨blk1 p g.1, hdetA⟩
      let B' : SpecialLinearGroup {i // ¬ p i} K := ⟨blk2 p g.1, hdetB⟩
      have hg : g = extHom1 p A' * extHom2 p B' := Subtype.ext (by
        rw [SpecialLinearGroup.coe_mul]
        exact hsplit)
      have hA : extHom1 p A' ∈ Subgroup.closure (elemSet cls) := by
        have h1 : A' ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
            Matrix.TransvectionStruct {i // p i} K → SpecialLinearGroup {i // p i} K)) := by
          rw [SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
          exact Subgroup.mem_top _
        have h2 := Subgroup.mem_map_of_mem (extHom1 p) h1
        rw [MonoidHom.map_closure] at h2
        refine (Subgroup.closure_mono ?_) h2
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        refine ⟨t.i.1, t.j.1, fun h => t.hij (Subtype.ext h), t.c, ?_, ?_⟩
        · exact t.i.2.trans t.j.2.symm
        · exact extHom1_transvection p t.hij t.c
      have hB : extHom2 p B' ∈ Subgroup.closure (elemSet cls) := by
        let cls' : {i // ¬ p i} → κ := fun x => cls x.1
        have hbd' : ∀ i j, cls' i ≠ cls' j → B'.1 i j = 0 := fun i j hij => hbd i.1 j.1 hij
        have hdet' : ∀ k : κ, (B'.1.submatrix (Subtype.val : {i // cls' i = k} → {i // ¬ p i})
            Subtype.val).det = 1 := by
          intro k
          by_cases hk : k = κ₀
          · have : IsEmpty {i : {i // ¬ p i} // cls' i = k} :=
              ⟨fun x => x.1.2 (x.2.trans hk)⟩
            exact Matrix.det_isEmpty
          · let e : {i : {i // ¬ p i} // cls' i = k} ≃ {i // cls i = k} :=
              { toFun := fun x => ⟨x.1.1, x.2⟩
                invFun := fun y => ⟨⟨y.1, fun h => hk (y.2.symm.trans h)⟩, y.2⟩
                left_inv := fun x => rfl
                right_inv := fun y => rfl }
            have := Matrix.det_submatrix_equiv_self e (g.1.submatrix (Subtype.val : {i // cls i = k} → m)
              Subtype.val)
            have h2 : (B'.1.submatrix (Subtype.val : {i : {i // ¬ p i} // cls' i = k} →
                {i // ¬ p i}) Subtype.val) =
                (g.1.submatrix (Subtype.val : {i // cls i = k} → m) Subtype.val).submatrix e e := rfl
            rw [h2, this]
            exact hdet k
        have := ih _ hcard {i // ¬ p i} rfl cls' B' hbd' hdet'
        have h2 := Subgroup.mem_map_of_mem (extHom2 p) this
        rw [MonoidHom.map_closure] at h2
        refine (Subgroup.closure_mono ?_) h2
        rintro _ ⟨_, ⟨i, j, hij, a, hcij, rfl⟩, rfl⟩
        refine ⟨i.1, j.1, fun h => hij (Subtype.ext h), a, hcij, ?_⟩
        exact extHom2_transvection p hij a
      rw [hg]
      exact Subgroup.mul_mem _ hA hB

theorem bd_mem_closure {m : Type} [Fintype m] [DecidableEq m] {κ : Type} [DecidableEq κ]
    (cls : m → κ) (g : SpecialLinearGroup m K) (hbd : ∀ i j, cls i ≠ cls j → g.1 i j = 0)
    (hdet : ∀ k : κ, (g.1.submatrix (Subtype.val : {i // cls i = k} → m) Subtype.val).det = 1) :
    g ∈ Subgroup.closure (elemSet cls) :=
  bd_mem_closure_aux _ m rfl cls g hbd hdet

end Main

end CFSG.RankThree.PartOne.KFCL.BlockSL

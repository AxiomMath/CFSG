module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProof

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Numbering

variable {Λ : Type*} {n : ℕ}

@[expose] def ggLastEquiv (e : Fin n ≃ Λ) : Fin (n + 1) ≃ Option Λ :=
  finSuccEquivLast.trans (Equiv.optionCongr e)

@[simp] theorem ggLastEquiv_castSucc (e : Fin n ≃ Λ) (i : Fin n) :
    ggLastEquiv e (Fin.castSucc i) = some (e i) := by
  simp [ggLastEquiv, finSuccEquivLast_castSucc]

@[simp] theorem ggLastEquiv_last (e : Fin n ≃ Λ) : ggLastEquiv e (Fin.last n) = none := by
  simp [ggLastEquiv, finSuccEquivLast_last]

@[expose] def ggFirstEquiv (e : Fin n ≃ Λ) : Fin (n + 1) ≃ Option Λ :=
  (finSuccEquiv n).trans (Equiv.optionCongr e)

@[simp] theorem ggFirstEquiv_zero (e : Fin n ≃ Λ) : ggFirstEquiv e 0 = none := by
  simp [ggFirstEquiv, finSuccEquiv_zero]

@[simp] theorem ggFirstEquiv_succ (e : Fin n ≃ Λ) (i : Fin n) :
    ggFirstEquiv e i.succ = some (e i) := by
  simp [ggFirstEquiv, finSuccEquiv_succ]

theorem ggMatrix_eq_reindex {ι κ : Type*} {P : Matrix κ κ ℤ} {Q : Matrix ι ι ℤ} (f : ι ≃ κ)
    (h : ∀ i j, P (f i) (f j) = Q i j) : P = Matrix.reindex f f Q := by
  ext γ γ'
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, ← h, f.apply_symm_apply, f.apply_symm_apply]

end Numbering

@[expose] def GGForkShapeA {Λ : Type*} (C : Matrix Λ Λ ℤ) (b : Λ) : Prop :=
  ∃ (m : ℕ) (e : Fin (m + 1) ≃ Λ), 2 ≤ m ∧ e (Fin.last m) = b ∧
    ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j

section ShapeA

variable {Λ : Type*} {C : Matrix Λ Λ ℤ} {m : ℕ} {e : Fin (m + 1) ≃ Λ}

theorem eq_of_forkShapeA (hm : 1 ≤ m) {b c : Λ} (hb : e (Fin.last m) = b)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) (hbc : C b c = -1) :
    c = e ⟨m - 1, by omega⟩ := by
  have h := hC (Fin.last m) (e.symm c)
  rw [hb, e.apply_symm_apply, hbc] at h
  have hk := (e.symm c).isLt
  have hval : ((e.symm c) : ℕ) = m - 1 := by
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_last] at h
    split_ifs at h
    omega
  rw [← e.apply_symm_apply c]
  exact congrArg e (Fin.ext hval)

variable [DecidableEq Λ]

theorem ggAttachCartan_forkShapeA_c (hm : 2 ≤ m)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) :
    ggAttachCartan C (e ⟨m - 1, by omega⟩) =
      Matrix.reindex (ggLastEquiv e) (ggLastEquiv e) (CartanMatrix.D (m + 2)) := by
  refine ggMatrix_eq_reindex _ fun i j => ?_
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [CartanMatrix.D]
    | cast j =>
      have hj := j.isLt
      simp only [ggLastEquiv_last, ggLastEquiv_castSucc, ggAttachCartan_none_some,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,
        Fin.val_last, Fin.val_castSucc, or_true, and_true]
      split_ifs <;> omega
  | cast i =>
    have hi := i.isLt
    induction j using Fin.lastCases with
    | last =>
      simp only [ggLastEquiv_last, ggLastEquiv_castSucc, ggAttachCartan_some_none,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,
        Fin.val_last, Fin.val_castSucc, or_true, and_true]
      split_ifs <;> omega
    | cast j =>
      have hj := j.isLt
      simp only [ggLastEquiv_castSucc, ggAttachCartan_some_some, hC, CartanMatrix.A,
        CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc]
      split_ifs <;> omega

theorem ggAttachCartan_forkShapeA_b (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) :
    ggAttachCartan C (e (Fin.last m)) =
      Matrix.reindex (ggLastEquiv e) (ggLastEquiv e) (CartanMatrix.A (m + 2)) := by
  refine ggMatrix_eq_reindex _ fun i j => ?_
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [CartanMatrix.A]
    | cast j =>
      have hj := j.isLt
      simp only [ggLastEquiv_last, ggLastEquiv_castSucc, ggAttachCartan_none_some,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff,
        Fin.val_last, Fin.val_castSucc]
      split_ifs <;> omega
  | cast i =>
    have hi := i.isLt
    induction j using Fin.lastCases with
    | last =>
      simp only [ggLastEquiv_last, ggLastEquiv_castSucc, ggAttachCartan_some_none,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff,
        Fin.val_last, Fin.val_castSucc]
      split_ifs <;> omega
    | cast j =>
      have hj := j.isLt
      simp only [ggLastEquiv_castSucc, ggAttachCartan_some_some, hC, CartanMatrix.A,
        Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc]

end ShapeA

section Weyl

variable {Λ : Type} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {m : ℕ} {e : Fin (m + 1) ≃ Λ}

theorem exists_weyl_ggAttachCartan_forkShapeA_c (hm : 2 ≤ m)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) :
    ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
      GGIntCartan M' (ggAttachCartan C (e ⟨m - 1, by omega⟩)) :=
  ⟨(ggCoxeterMatrixD (m + 2)).reindex (ggLastEquiv e),
    Or.inl ⟨m + 2, ggLastEquiv e, by omega, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩,
    by rw [ggAttachCartan_forkShapeA_c hm hC]; exact (ggIntCartan_D (m + 2)).reindex _⟩

theorem exists_weyl_ggAttachCartan_forkShapeA_b
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) :
    ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
      GGIntCartan M' (ggAttachCartan C (e (Fin.last m))) :=
  ⟨(CoxeterMatrix.A (m + 2)).reindex (ggLastEquiv e),
    Or.inl ⟨m + 2, ggLastEquiv e, by omega, Or.inl rfl⟩,
    by rw [ggAttachCartan_forkShapeA_b hC]; exact (ggIntCartan_A (m + 2)).reindex _⟩

end Weyl

section Chain

variable {Λ : Type*} {C : Matrix Λ Λ ℤ} {m : ℕ} {e : Fin (m + 1) ≃ Λ}

@[expose] def ggForkChainA (e : Fin (m + 1) ≃ Λ) (j : ℕ) : Λ :=
  e ⟨min j m, Nat.lt_succ_of_le (Nat.min_le_right j m)⟩

theorem ggForkChainA_of_lt {j : ℕ} (hj : j < m) : ggForkChainA e j = e ⟨j, by omega⟩ := by
  simp [ggForkChainA, Nat.min_eq_left hj.le]

variable [DecidableEq Λ]

theorem ggChainPairing_of_forkShapeA {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V}
    {b c : Λ} (hF : GGForkPairing C b c h α ha αa) (hm : 1 ≤ m) (hb : e (Fin.last m) = b)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A (m + 1) i j) :
    GGChainPairing m (h ∘ ggForkChainA e) (α ∘ ggForkChainA e) ha αa ∧
      GGChainPairing m (h ∘ ggForkChainA e) (α ∘ ggForkChainA e) (h b) (α b) := by
  have hc : c = e ⟨m - 1, by omega⟩ :=
    eq_of_forkShapeA hm hb hC (by rw [hF.bL c hF.ne.symm, ite_eq_left rfl])
  have hne : ∀ j (hj : j < m), e ⟨j, by omega⟩ ≠ b := fun j hj h' => by
    rw [← hb] at h'
    have := congrArg Fin.val (e.injective h')
    simp only [Fin.val_last] at this
    omega
  have hcj : ∀ j (hj : j < m), (e ⟨j, by omega⟩ = c ↔ j + 1 = m) := fun j hj => by
    rw [hc, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq]
    omega
  have hjj : ∀ j k, j < m → k < m → (α ∘ ggForkChainA e) j ((h ∘ ggForkChainA e) k) =
      if j = k then 2 else if j + 1 = k ∨ k + 1 = j then -1 else 0 := by
    intro j k hj hk
    simp only [Function.comp_apply, ggForkChainA_of_lt hj, ggForkChainA_of_lt hk, hF.pair, hC,
      CartanMatrix.A, Matrix.of_apply, Fin.mk.injEq]
    split_ifs <;> simp
  refine ⟨⟨hjj, fun j hj => ?_, fun j hj => ?_, hF.aa⟩, ⟨hjj, fun j hj => ?_, fun j hj => ?_,
    hF.self b⟩⟩
  · simp only [Function.comp_apply, ggForkChainA_of_lt hj, hF.aR _ (hne j hj)]
    by_cases h' : j + 1 = m
    · rw [ite_eq_left ((hcj j hj).mpr h'), ite_eq_left h']
    · rw [ite_eq_right (fun h'' => h' ((hcj j hj).mp h'')), ite_eq_right h']
  · simp only [Function.comp_apply, ggForkChainA_of_lt hj, hF.aL _ (hne j hj)]
    by_cases h' : j + 1 = m
    · rw [ite_eq_left ((hcj j hj).mpr h'), ite_eq_left h']
    · rw [ite_eq_right (fun h'' => h' ((hcj j hj).mp h'')), ite_eq_right h']
  · simp only [Function.comp_apply, ggForkChainA_of_lt hj, hF.pair, hF.bR _ (hne j hj)]
    by_cases h' : j + 1 = m
    · rw [ite_eq_left ((hcj j hj).mpr h'), ite_eq_left h']
      simp
    · rw [ite_eq_right (fun h'' => h' ((hcj j hj).mp h'')), ite_eq_right h']
      simp
  · simp only [Function.comp_apply, ggForkChainA_of_lt hj, hF.pair, hF.bL _ (hne j hj)]
    by_cases h' : j + 1 = m
    · rw [ite_eq_left ((hcj j hj).mpr h'), ite_eq_left h']
      simp
    · rw [ite_eq_right (fun h'' => h' ((hcj j hj).mp h'')), ite_eq_right h']
      simp

omit [DecidableEq Λ] in
theorem range_eq_of_forkShapeA {X : Type*} (φ : Λ → X) {b : Λ} (hb : e (Fin.last m) = b) :
    Set.range φ = (φ ∘ ggForkChainA e) '' Set.Iio m ∪ {φ b} := by
  ext ψ
  simp only [Set.mem_range, Set.mem_union, Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff,
    Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨k, rfl⟩ := e.surjective i
    by_cases hk : k = Fin.last m
    · exact Or.inr (by rw [hk, hb])
    · have hk' : (k : ℕ) < m := Fin.val_lt_last hk
      exact Or.inl ⟨k, hk', by rw [ggForkChainA_of_lt hk']⟩
  · rintro (⟨j, -, rfl⟩ | rfl)
    · exact ⟨_, rfl⟩
    · exact ⟨b, rfl⟩

omit [DecidableEq Λ] in
theorem image_ne_eq_of_forkShapeA {X : Type*} (φ : Λ → X) {b : Λ} (hb : e (Fin.last m) = b) :
    φ '' {i | i ≠ b} = (φ ∘ ggForkChainA e) '' Set.Iio m := by
  ext ψ
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_Iio, Function.comp_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨k, rfl⟩ := e.surjective i
    have hk : k ≠ Fin.last m := fun h' => hi (by rw [h', hb])
    have hk' : (k : ℕ) < m := Fin.val_lt_last hk
    exact ⟨k, hk', by rw [ggForkChainA_of_lt hk']⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨_, ?_, rfl⟩
    rw [ggForkChainA_of_lt hj]
    intro h'
    rw [← hb] at h'
    have := congrArg Fin.val (e.injective h')
    simp only [Fin.val_last] at this
    omega

end Chain

theorem ggForkLabel_of_forkShapeA (hX : GGTypeACrossLabelInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hOp : GGOpAutTrivial p Bs) (hID : GGInnerDiagAll p B Bs x L D J)
    (hNT : GGNoTransvection p Bs) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K)
    (hsc : GGScalarsOrWeyl' p B Bs x D J) [Fact p.Prime] {Λ : Type} [DecidableEq Λ]
    {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Λ → MulAut ↥Bs} {φa : MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    {ha : V} {αa : Module.Dual (ZMod p) V} {b c : Λ} (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hK : ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}))
    (hA : GGForkShapeA C b) :
    (αa (h b) = 0 ∧ ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
        GGIntCartan M' (ggAttachCartan C c)) ∨
      (αa (h b) = 1 ∧ ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
        GGIntCartan M' (ggAttachCartan C b)) := by
  obtain ⟨m, e, hm, hb, hC⟩ := hA
  have hc : c = e ⟨m - 1, by omega⟩ :=
    eq_of_forkShapeA (by omega) hb hC (by rw [hF.bL c hF.ne.symm, ite_eq_left rfl])
  obtain ⟨hPa, hPb⟩ := ggChainPairing_of_forkShapeA hF (by omega) hb hC
  have hL' : ggAutomizer L Bs =
      Subgroup.closure ((φ ∘ ggForkChainA e) '' Set.Iio m ∪ {φ b}) := by
    rw [hL, range_eq_of_forkShapeA φ hb]
  have hK' : ggAutomizer K Bs =
      Subgroup.closure ((φ ∘ ggForkChainA e) '' Set.Iio m ∪ {φa}) := by
    rw [hK, image_ne_eq_of_forkShapeA φ hb]
  rcases hX G p B Bs x L D J hcfg hOp hID hNT y K hnbr hsc V ι m hm (φ ∘ ggForkChainA e) φa (φ b)
      (h ∘ ggForkChainA e) (α ∘ ggForkChainA e) ha (h b) αa (α b) hPa hPb
      (fun j _ w => hlin (ggForkChainA e j) w) hlina (hlin b) hL' hK' with hu | hu
  · exact Or.inl ⟨hu, by rw [hc]; exact exists_weyl_ggAttachCartan_forkShapeA_c hm hC⟩
  · exact Or.inr ⟨hu, by rw [← hb]; exact exists_weyl_ggAttachCartan_forkShapeA_b hC⟩

end CFSG.StandardType

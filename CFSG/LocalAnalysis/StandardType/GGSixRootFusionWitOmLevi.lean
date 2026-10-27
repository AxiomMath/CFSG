module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmMat
public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock

public section

namespace CFSG.StandardType

namespace WitOm

open Module QuadraticMap CFSG.Assembly Matrix

variable {K : Type} [Field K] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι']

section Levi

@[expose] def leviMat (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B : Matrix (Fin 2) (Fin 2) K) :
    Matrix ι ι K :=
  Matrix.reindex e.symm e.symm (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B) 0 0 1)

omit [DecidableEq ι] [DecidableEq ι'] in
theorem reindex_mul_reindex {α β : Type} [Fintype α] [Fintype β] (f : α ≃ β)
    (M N : Matrix α α K) :
    Matrix.reindex f f M * Matrix.reindex f f N = Matrix.reindex f f (M * N) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]

omit [DecidableEq ι] in
theorem leviMat_mul (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B A' B' : Matrix (Fin 2) (Fin 2) K) :
    leviMat e A B * leviMat e A' B' = leviMat e (A * A') (B * B') := by
  rw [leviMat, leviMat, leviMat, reindex_mul_reindex, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

omit [Fintype ι] [Fintype ι'] in
theorem leviMat_one (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') :
    leviMat e (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [leviMat, Matrix.fromBlocks_one, Matrix.fromBlocks_one]
  simp

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] in
theorem leviMat_apply (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B : Matrix (Fin 2) (Fin 2) K) (x y : ι) :
    leviMat e A B x y = Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B) 0 0 1 (e x) (e y) := by
  rw [leviMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]

@[expose] noncomputable def leviHom (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') : GL (Fin 2) K →* GL ι K where
  toFun A := ⟨leviMat e (A : Matrix (Fin 2) (Fin 2) K) ((A⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)ᵀ, leviMat e ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      (A : Matrix (Fin 2) (Fin 2) K)ᵀ, by
    rw [leviMat_mul, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, leviMat_one], by
    rw [leviMat_mul, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, leviMat_one]⟩
  map_one' := Units.ext (by
    change leviMat e _ _ = 1
    rw [inv_one, Units.val_one, Matrix.transpose_one, leviMat_one])
  map_mul' A B := Units.ext (by
    change leviMat e _ _ = leviMat e _ _ * leviMat e _ _
    rw [leviMat_mul, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.transpose_mul])

theorem coe_leviHom (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A : GL (Fin 2) K) :
    ((leviHom e A : GL ι K) : Matrix ι ι K) = leviMat e (A : Matrix (Fin 2) (Fin 2) K)
      ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ :=
  rfl

theorem leviHom_injective (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') :
    Function.Injective (leviHom (K := K) e) := by
  intro A A' h
  apply Units.ext
  ext i j
  have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) (e.symm (.inl (.inl i)))
    (e.symm (.inl (.inl j)))) h
  simpa [coe_leviHom, leviMat_apply] using h1

omit [DecidableEq ι] in
theorem leviMat_mulVec (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B : Matrix (Fin 2) (Fin 2) K)
    (v : ι → K) (z : (Fin 2 ⊕ Fin 2) ⊕ ι') :
    (leviMat e A B *ᵥ v) (e.symm z) =
      (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B) 0 0 1 *ᵥ (v ∘ e.symm)) z := by
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, ← Equiv.sum_comp e]
  simp [leviMat_apply]

omit [DecidableEq ι] in
theorem leviMat_mulVec_aa (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B : Matrix (Fin 2) (Fin 2) K)
    (v : ι → K) (i : Fin 2) :
    (leviMat e A B *ᵥ v) (e.symm (.inl (.inl i))) = ∑ j, A i j * v (e.symm (.inl (.inl j))) := by
  rw [leviMat_mulVec, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inl, Matrix.zero_mulVec, add_zero, Matrix.fromBlocks_mulVec]
  rw [Matrix.mulVec, dotProduct]
  rfl

omit [DecidableEq ι] in
theorem leviMat_mulVec_bb (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B : Matrix (Fin 2) (Fin 2) K)
    (v : ι → K) (i : Fin 2) :
    (leviMat e A B *ᵥ v) (e.symm (.inl (.inr i))) = ∑ j, B i j * v (e.symm (.inl (.inr j))) := by
  rw [leviMat_mulVec, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inl, Matrix.zero_mulVec, add_zero, Matrix.fromBlocks_mulVec,
    Sum.elim_inr, zero_add]
  rw [Matrix.mulVec, dotProduct]
  rfl

omit [DecidableEq ι] in
theorem leviMat_mulVec_r (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B : Matrix (Fin 2) (Fin 2) K)
    (v : ι → K) (x : ι') : (leviMat e A B *ᵥ v) (e.symm (.inr x)) = v (e.symm (.inr x)) := by
  rw [leviMat_mulVec, Matrix.fromBlocks_mulVec]
  simp

omit [DecidableEq ι] in
theorem leviMat_isometry (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = (∑ i, v (e.symm (.inl (.inl i))) * v (e.symm (.inl (.inr i)))) +
      Q' fun x => v (e.symm (.inr x)))
    {A B : Matrix (Fin 2) (Fin 2) K} (hAB : Aᵀ * B = 1) (v : ι → K) :
    Q (leviMat e A B *ᵥ v) = Q v := by
  rw [hQ, hQ]
  simp only [leviMat_mulVec_aa, leviMat_mulVec_bb, leviMat_mulVec_r, Fin.sum_univ_two]
  have h00 := congrFun (congrFun hAB 0) 0
  have h01 := congrFun (congrFun hAB 0) 1
  have h10 := congrFun (congrFun hAB 1) 0
  have h11 := congrFun (congrFun hAB 1) 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  set x₀ := v (e.symm (.inl (.inl 0)))
  set x₁ := v (e.symm (.inl (.inl 1)))
  set y₀ := v (e.symm (.inl (.inr 0)))
  set y₁ := v (e.symm (.inl (.inr 1)))
  linear_combination (x₀ * y₀) * h00 + (x₀ * y₁) * h01 + (x₁ * y₀) * h10 + (x₁ * y₁) * h11

theorem leviHom_mem_orth (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {Q : (ι → K) → K}
    {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = (∑ i, v (e.symm (.inl (.inl i))) * v (e.symm (.inl (.inr i)))) +
      Q' fun x => v (e.symm (.inr x))) (A : GL (Fin 2) K) :
    leviHom e A ∈ LargeEvenOrthGroup Q := by
  refine TableBSymp.mem_orthGroup_of_isometry fun v => ?_
  rw [coe_leviHom]
  refine leviMat_isometry e hQ ?_ v
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

end Levi

section Cent

@[expose] def leviMat3 (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B : Matrix (Fin 2) (Fin 2) K)
    (C : Matrix ι' ι' K) : Matrix ι ι K :=
  Matrix.reindex e.symm e.symm (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B) 0 0 C)

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem leviMat3_apply (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B : Matrix (Fin 2) (Fin 2) K)
    (C : Matrix ι' ι' K) (x y : ι) :
    leviMat3 e A B C x y = Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B) 0 0 C (e x) (e y) := by
  rw [leviMat3, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] in
theorem leviMat_eq_leviMat3 (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B : Matrix (Fin 2) (Fin 2) K) :
    leviMat e A B = leviMat3 e A B 1 :=
  rfl

omit [DecidableEq ι] [DecidableEq ι'] in
theorem leviMat3_mul (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') (A B A' B' : Matrix (Fin 2) (Fin 2) K)
    (C C' : Matrix ι' ι' K) :
    leviMat3 e A B C * leviMat3 e A' B' C' = leviMat3 e (A * A') (B * B') (C * C') := by
  rw [leviMat3, leviMat3, leviMat3, reindex_mul_reindex, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem leviMat3_inj (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {A B A' B' : Matrix (Fin 2) (Fin 2) K}
    {C C' : Matrix ι' ι' K} (h : leviMat3 e A B C = leviMat3 e A' B' C') :
    A = A' ∧ B = B' ∧ C = C' := by
  have hre : ∀ M : Matrix ((Fin 2 ⊕ Fin 2) ⊕ ι') ((Fin 2 ⊕ Fin 2) ⊕ ι') K,
      Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := fun M => by
    rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]
  have h' := congrArg (Matrix.reindex e e) h
  rw [leviMat3, leviMat3, hre, hre, Matrix.fromBlocks_inj, Matrix.fromBlocks_inj] at h'
  exact ⟨h'.1.1, h'.1.2.2.2, h'.2.2.2⟩

omit [Fintype ι'] [DecidableEq ι'] in
theorem exists_leviMat3_of_commute (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {δ : ι → Kˣ} {ζ : Kˣ}
    (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ ζ⁻¹) (hδa : ∀ i, δ (e.symm (.inl (.inl i))) = ζ)
    (hδb : ∀ i, δ (e.symm (.inl (.inr i))) = ζ⁻¹) (hδr : ∀ x, δ (e.symm (.inr x)) = 1)
    {c : GL ι K} (hc : c * TauCeti.diagGL δ = TauCeti.diagGL δ * c) :
    ∃ A B C, (c : Matrix ι ι K) = leviMat3 e A B C := by
  have hc' := TableBOrth.commute_diagGL_iff.mp hc
  have h0 : ∀ x y, (δ x : K) ≠ δ y → (c : Matrix ι ι K) x y = 0 := fun x y h =>
    TableBOrth.eq_zero_of_commute_diagonal hc' h
  have hne : ∀ {u u' : Kˣ}, u ≠ u' → (u : K) ≠ u' := fun h h' => h (Units.ext h')
  have h1 : (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := hne hζ2
  have h2 : (ζ : K) ≠ ((1 : Kˣ) : K) := hne hζ1
  have h3 : ((ζ⁻¹ : Kˣ) : K) ≠ ((1 : Kˣ) : K) := hne (inv_ne_one.mpr hζ1)
  set A₀ : Matrix (Fin 2) (Fin 2) K :=
    fun i j => (c : Matrix ι ι K) (e.symm (.inl (.inl i))) (e.symm (.inl (.inl j)))
  set B₀ : Matrix (Fin 2) (Fin 2) K :=
    fun i j => (c : Matrix ι ι K) (e.symm (.inl (.inr i))) (e.symm (.inl (.inr j)))
  set C₀ : Matrix ι' ι' K := fun x y => (c : Matrix ι ι K) (e.symm (.inr x)) (e.symm (.inr y))
  have key : Matrix.reindex e e (c : Matrix ι ι K) =
      Matrix.fromBlocks (Matrix.fromBlocks A₀ 0 0 B₀) 0 0 C₀ := by
    ext z w
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases z with (i | i) | x <;> rcases w with (j | j) | y <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    · rfl
    · exact h0 _ _ (by rw [hδa, hδb]; exact h1)
    · exact h0 _ _ (by rw [hδa, hδr]; exact h2)
    · exact h0 _ _ (by rw [hδb, hδa]; exact h1.symm)
    · rfl
    · exact h0 _ _ (by rw [hδb, hδr]; exact h3)
    · exact h0 _ _ (by rw [hδr, hδa]; exact h2.symm)
    · exact h0 _ _ (by rw [hδr, hδb]; exact h3.symm)
    · rfl
  refine ⟨A₀, B₀, C₀, ?_⟩
  rw [leviMat3, ← key, ← Matrix.reindex_symm, Equiv.symm_apply_apply]

theorem exists_conj_leviMat (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {δ : ι → Kˣ} {ζ : Kˣ}
    (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ ζ⁻¹) (hδa : ∀ i, δ (e.symm (.inl (.inl i))) = ζ)
    (hδb : ∀ i, δ (e.symm (.inl (.inr i))) = ζ⁻¹) (hδr : ∀ x, δ (e.symm (.inr x)) = 1)
    {c : GL ι K} (hc : c * TauCeti.diagGL δ = TauCeti.diagGL δ * c)
    (A B : Matrix (Fin 2) (Fin 2) K) :
    ∃ A' B', (c : Matrix ι ι K) * leviMat e A B * ((c⁻¹ : GL ι K) : Matrix ι ι K) =
      leviMat e A' B' := by
  have hci : c⁻¹ * TauCeti.diagGL δ = TauCeti.diagGL δ * c⁻¹ := by
    calc c⁻¹ * TauCeti.diagGL δ = c⁻¹ * (TauCeti.diagGL δ * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * TauCeti.diagGL δ) * c⁻¹ := by rw [hc]
      _ = TauCeti.diagGL δ * c⁻¹ := by group
  obtain ⟨c₁, c₂, c₃, hc₁⟩ := exists_leviMat3_of_commute e hζ1 hζ2 hδa hδb hδr hc
  obtain ⟨c₁', c₂', c₃', hc₂⟩ := exists_leviMat3_of_commute e hζ1 hζ2 hδa hδb hδr hci
  have h1 : leviMat3 e (c₁ * c₁') (c₂ * c₂') (c₃ * c₃') = leviMat3 e 1 1 1 := by
    rw [← leviMat3_mul, ← hc₁, ← hc₂, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      ← leviMat_eq_leviMat3, leviMat_one]
  have h3 : c₃ * c₃' = 1 := (leviMat3_inj e h1).2.2
  refine ⟨c₁ * A * c₁', c₂ * B * c₂', ?_⟩
  rw [hc₁, hc₂, leviMat_eq_leviMat3, leviMat3_mul, leviMat3_mul, mul_one, h3,
    ← leviMat_eq_leviMat3]

theorem mem_range_leviHom (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {Q : (ι → K) → K}
    {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = (∑ i, v (e.symm (.inl (.inl i))) * v (e.symm (.inl (.inr i)))) +
      Q' fun x => v (e.symm (.inr x)))
    {M : GL ι K} (hMO : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v)
    {A B : Matrix (Fin 2) (Fin 2) K} (hM : (M : Matrix ι ι K) = leviMat e A B) :
    M ∈ (leviHom e).range := by
  have hval : ∀ j l, ∑ i, A i j * B i l = if j = l then 1 else 0 := by
    intro j l
    have h := hMO (Pi.single (e.symm (.inl (.inl j))) 1 + Pi.single (e.symm (.inl (.inr l))) 1)
    rw [hM, hQ, hQ] at h
    simp only [leviMat_mulVec_aa, leviMat_mulVec_bb, leviMat_mulVec_r, Pi.add_apply,
      Pi.single_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      ite_false, add_zero, zero_add, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    rw [add_right_cancel h]
    by_cases hjl : j = l
    · subst hjl
      simp
    · simp [hjl, Ne.symm hjl]
  have hAB : Aᵀ * B = 1 := by
    ext j l
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    exact hval j l
  have hBA : B * Aᵀ = 1 := mul_eq_one_comm.mp hAB
  have h1 : A * Bᵀ = 1 := by
    have := congrArg Matrix.transpose hBA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h2 : Bᵀ * A = 1 := by
    have := congrArg Matrix.transpose hAB
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  refine ⟨⟨A, Bᵀ, h1, h2⟩, Units.ext ?_⟩
  rw [coe_leviHom, hM, Units.inv_mk, Units.val_mk, Matrix.transpose_transpose]

theorem conj_mem_range_leviHom (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {Q : (ι → K) → K}
    {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = (∑ i, v (e.symm (.inl (.inl i))) * v (e.symm (.inl (.inr i)))) +
      Q' fun x => v (e.symm (.inr x)))
    {δ : ι → Kˣ} {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ ζ⁻¹)
    (hδa : ∀ i, δ (e.symm (.inl (.inl i))) = ζ) (hδb : ∀ i, δ (e.symm (.inl (.inr i))) = ζ⁻¹)
    (hδr : ∀ x, δ (e.symm (.inr x)) = 1) {c : GL ι K} (hcO : c ∈ LargeEvenOrthGroup Q)
    (hc : c * TauCeti.diagGL δ = TauCeti.diagGL δ * c) {M : GL ι K}
    (hM : M ∈ (leviHom e).range) : c * M * c⁻¹ ∈ (leviHom e).range := by
  obtain ⟨A, rfl⟩ := hM
  obtain ⟨A', B', h⟩ := exists_conj_leviMat e hζ1 hζ2 hδa hδb hδr hc
    (A : Matrix (Fin 2) (Fin 2) K) ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ
  refine mem_range_leviHom e hQ (fun v => ?_) (A := A') (B := B') ?_
  · exact TableBOrth.isometry_of_mem_orthGroup
      (mul_mem (mul_mem hcO (leviHom_mem_orth e hQ A)) (inv_mem hcO)) v
  · rw [Units.val_mul, Units.val_mul, coe_leviHom]
    exact h

omit [Fintype ι'] in
theorem leviMat_commute (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {δ : ι → Kˣ} {ζ : Kˣ}
    (hδa : ∀ i, δ (e.symm (.inl (.inl i))) = ζ) (hδb : ∀ i, δ (e.symm (.inl (.inr i))) = ζ⁻¹)
    (hδr : ∀ x, δ (e.symm (.inr x)) = 1) (A B : Matrix (Fin 2) (Fin 2) K) :
    leviMat e A B * Matrix.diagonal (fun i => (δ i : K)) =
      Matrix.diagonal (fun i => (δ i : K)) * leviMat e A B := by
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  obtain ⟨z, rfl⟩ := e.symm.surjective x
  obtain ⟨w, rfl⟩ := e.symm.surjective y
  rw [leviMat_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rcases z with (i | i) | x <;> rcases w with (j | j) | y <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, mul_zero, hδa, hδb, hδr]
  · rw [mul_comm]
  · rw [mul_comm]
  · rw [Units.val_one, mul_one, one_mul]

end Cent

section Comp

@[expose] noncomputable def leviSL (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL ι K :=
  (leviHom e).comp Matrix.SpecialLinearGroup.toGL

theorem leviSL_injective (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') :
    Function.Injective (leviSL (K := K) e) :=
  (leviHom_injective e).comp Matrix.SpecialLinearGroup.toGL_injective

theorem range_leviSL_le_range (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') :
    (leviSL (K := K) e).range ≤ (leviHom e).range := by
  rintro _ ⟨X, rfl⟩
  exact ⟨_, rfl⟩

theorem range_leviSL_eq_commutator [Finite K] (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι')
    (h4 : 4 ≤ Nat.card K) :
    (leviSL (K := K) e).range = ⁅(leviSL (K := K) e).range, (leviSL (K := K) e).range⁆ := by
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ :=
    Group.isPerfect_def.mp (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4).1
  calc (leviSL (K := K) e).range = (⊤ : Subgroup _).map (leviSL e) := MonoidHom.range_eq_map _
    _ = (commutator (Matrix.SpecialLinearGroup (Fin 2) K)).map (leviSL e) := by rw [hperf]
    _ = ⁅(⊤ : Subgroup _).map (leviSL e), (⊤ : Subgroup _).map (leviSL e)⁆ := by
      rw [commutator_def, Subgroup.map_commutator]
    _ = ⁅(leviSL (K := K) e).range, (leviSL (K := K) e).range⁆ := by
      rw [← MonoidHom.range_eq_map]

theorem commutator_range_leviHom_le (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') :
    ⁅(leviHom (K := K) e).range, (leviHom (K := K) e).range⁆ ≤ (leviSL (K := K) e).range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def]
  have h1 : commutator (GL (Fin 2) K) ≤ (Matrix.SpecialLinearGroup.toGL).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact Abelianization.commutator_subset_ker _
  calc (commutator (GL (Fin 2) K)).map (leviHom e) ≤
        (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := K)).range.map (leviHom e) :=
      Subgroup.map_mono h1
    _ = (leviSL e).range := by rw [leviSL, MonoidHom.range_comp]

theorem range_leviSL_le_omega [Finite K] (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {Q : (ι → K) → K}
    {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = (∑ i, v (e.symm (.inl (.inl i))) * v (e.symm (.inl (.inr i)))) +
      Q' fun x => v (e.symm (.inr x))) (h4 : 4 ≤ Nat.card K) :
    (leviSL (K := K) e).range ≤ LargeEvenOmega Q := by
  have hO : (leviSL (K := K) e).range ≤ LargeEvenOrthGroup Q := by
    rintro _ ⟨X, rfl⟩
    exact leviHom_mem_orth e hQ _
  rw [range_leviSL_eq_commutator e h4]
  exact Subgroup.commutator_mono hO hO

theorem conj_mem_range_leviSL [Finite K] (e : ι ≃ (Fin 2 ⊕ Fin 2) ⊕ ι') {Q : (ι → K) → K}
    {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q v = (∑ i, v (e.symm (.inl (.inl i))) * v (e.symm (.inl (.inr i)))) +
      Q' fun x => v (e.symm (.inr x))) (h4 : 4 ≤ Nat.card K)
    {δ : ι → Kˣ} {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ ζ⁻¹)
    (hδa : ∀ i, δ (e.symm (.inl (.inl i))) = ζ) (hδb : ∀ i, δ (e.symm (.inl (.inr i))) = ζ⁻¹)
    (hδr : ∀ x, δ (e.symm (.inr x)) = 1) {c : GL ι K} (hcO : c ∈ LargeEvenOrthGroup Q)
    (hc : c * TauCeti.diagGL δ = TauCeti.diagGL δ * c) {y : GL ι K}
    (hy : y ∈ (leviSL (K := K) e).range) : c * y * c⁻¹ ∈ (leviSL (K := K) e).range := by
  have hmap : ((leviHom (K := K) e).range).map (MulAut.conj c).toMonoidHom ≤
      (leviHom e).range := by
    rintro _ ⟨M, hM, rfl⟩
    exact conj_mem_range_leviHom e hQ hζ1 hζ2 hδa hδb hδr hcO hc hM
  have hle : ((leviSL (K := K) e).range).map (MulAut.conj c).toMonoidHom ≤ (leviHom e).range :=
    (Subgroup.map_mono (range_leviSL_le_range e)).trans hmap
  rw [range_leviSL_eq_commutator e h4] at hy
  have hmem : c * y * c⁻¹ ∈ (⁅(leviSL (K := K) e).range, (leviSL (K := K) e).range⁆).map
      (MulAut.conj c).toMonoidHom := ⟨y, hy, by simp [MulAut.conj_apply]⟩
  rw [Subgroup.map_commutator] at hmem
  exact commutator_range_leviHom_le e (Subgroup.commutator_mono hle hle hmem)

end Comp

end WitOm

end CFSG.StandardType

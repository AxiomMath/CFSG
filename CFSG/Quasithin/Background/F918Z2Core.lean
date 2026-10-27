module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.SwapModel

open scoped Matrix

variable {F : Type} [Field F] {d r : ℕ}

theorem exists_mulVec_ne_zero {m n : Type*} [Fintype n] [DecidableEq n] {A : Matrix m n F}
    (hA : A ≠ 0) : ∃ w, A.mulVec w ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hA (Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, Matrix.zero_mulVec])

theorem ext_of_mulVec_single {m n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix m n F}
    (h : ∀ i, X.mulVec (Pi.single i 1) = Y.mulVec (Pi.single i 1)) : X = Y := by
  ext k i
  have := congrFun (h i) k
  simpa [Matrix.mulVec_single_one] using this

theorem eq_mul_mul_inv_of_mul_eq {n : Type*} [Fintype n] [DecidableEq n] {T B A : Matrix n n F}
    (hT : IsUnit T) (h : B * T = T * A) : B = T * A * T⁻¹ := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv T hdet, Matrix.mul_one]

theorem isUnit_right_of_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n F}
    (h : A * B = 1) : IsUnit B := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one_right _ this

theorem isUnit_left_of_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n F}
    (h : A * B = 1) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this

theorem isUnit_transpose {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n F}
    (h : IsUnit A) : IsUnit Aᵀ := by
  rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
  rwa [Matrix.det_transpose]

theorem exists_matrix_intertwiner (hd : 0 < d)
    (γ : Matrix (Fin d) (Fin d) F →+* Matrix (Fin r) (Fin r) F)
    (hγ : ∀ (c : F) (A : Matrix (Fin d) (Fin d) F), γ (c • A) = c • γ A)
    (hinj : Function.Injective γ) :
    ∃ T : Matrix (Fin r) (Fin d) F, Function.Injective T.mulVec ∧ ∀ A, γ A * T = T * A := by
  classical
  let i₀ : Fin d := ⟨0, hd⟩
  have he0 : γ (Matrix.single i₀ i₀ (1 : F)) ≠ 0 := by
    intro h0
    have h1 : Matrix.single i₀ i₀ (1 : F) = 0 := hinj (by rw [h0, map_zero])
    have h2 := congrFun (congrFun h1 i₀) i₀
    simp at h2
  have hee : γ (Matrix.single i₀ i₀ (1 : F)) * γ (Matrix.single i₀ i₀ (1 : F)) =
      γ (Matrix.single i₀ i₀ (1 : F)) := by
    rw [← map_mul, Matrix.single_mul_single_same, mul_one]
  obtain ⟨w, hw⟩ := exists_mulVec_ne_zero he0
  set w₁ := (γ (Matrix.single i₀ i₀ (1 : F))).mulVec w with hw₁
  have hw₁0 : w₁ ≠ 0 := hw
  have hew₁ : (γ (Matrix.single i₀ i₀ (1 : F))).mulVec w₁ = w₁ := by
    rw [hw₁, Matrix.mulVec_mulVec, hee]
  let T : Matrix (Fin r) (Fin d) F :=
    Matrix.of fun k i => (γ (Matrix.single i i₀ (1 : F))).mulVec w₁ k
  have hT_col : ∀ i, T.mulVec (Pi.single i 1) = (γ (Matrix.single i i₀ (1 : F))).mulVec w₁ := by
    intro i
    rw [Matrix.mulVec_single_one]
    rfl
  have hT_col0 : T.mulVec (Pi.single i₀ 1) = w₁ := by rw [hT_col, hew₁]
  have hunit : ∀ l m, γ (Matrix.single l m (1 : F)) * T = T * Matrix.single l m (1 : F) := by
    intro l m
    refine ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT_col, Matrix.mulVec_mulVec, ← map_mul,
      Matrix.single_mulVec_eq]
    by_cases h : m = i
    · subst h
      rw [Matrix.single_mul_single_same, Matrix.mulVec_smul, hT_col]
      simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h _, map_zero, Matrix.zero_mulVec,
        Matrix.mulVec_smul]
      simp [h]
  have hmat : ∀ A, γ A * T = T * A := by
    intro A
    induction A using Matrix.induction_on' with
    | h_zero => simp
    | h_add p q hp hq => rw [map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
    | h_std_basis l m x =>
        have hx : Matrix.single l m x = x • Matrix.single l m (1 : F) := by simp
        rw [hx, hγ, Matrix.smul_mul, Matrix.mul_smul, hunit]
  have hker : ∀ a, T.mulVec a = 0 → a = 0 := by
    intro a ha
    ext j
    have h1 := congrArg (fun M => M.mulVec a) (hunit i₀ j)
    simp only [← Matrix.mulVec_mulVec, ha, Matrix.mulVec_zero] at h1
    rw [Matrix.single_mulVec_eq, Matrix.mulVec_smul, hT_col0] at h1
    rcases smul_eq_zero.mp h1.symm with h | h
    · simpa using h
    · exact absurd h hw₁0
  refine ⟨T, fun a b hab => ?_, hmat⟩
  have : T.mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
  exact sub_eq_zero.mp (hker _ this)

theorem surjective_mulVec_of_irr (hd : 0 < d)
    {γ : Matrix (Fin d) (Fin d) F →+* Matrix (Fin r) (Fin r) F}
    {T : Matrix (Fin r) (Fin d) F} (hTi : Function.Injective T.mulVec)
    (hT : ∀ A, γ A * T = T * A)
    (hirr : ∀ W : Submodule F (Fin r → F), (∀ A, ∀ w ∈ W, (γ A).mulVec w ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Function.Surjective T.mulVec := by
  let W : Submodule F (Fin r → F) := LinearMap.range (Matrix.mulVecLin T)
  have hW : ∀ A, ∀ w ∈ W, (γ A).mulVec w ∈ W := by
    rintro A _ ⟨a, rfl⟩
    refine ⟨A.mulVec a, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hT]
  classical
  rcases hirr W hW with h | h
  · exfalso
    have h0 : T.mulVec (Pi.single ⟨0, hd⟩ 1) ∈ W := ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at h0
    have h1 : T.mulVec (Pi.single ⟨0, hd⟩ 1) = T.mulVec 0 := by rw [h0, Matrix.mulVec_zero]
    have h2 := congrFun (hTi h1) ⟨0, hd⟩
    simp at h2
  · intro w
    have hw : w ∈ W := by rw [h]; trivial
    obtain ⟨a, ha⟩ := hw
    exact ⟨a, ha⟩

theorem eq_of_bijective_mulVec {T : Matrix (Fin r) (Fin d) F} (hi : Function.Injective T.mulVec)
    (hs : Function.Surjective T.mulVec) : r = d := by
  have e : (Fin d → F) ≃ₗ[F] (Fin r → F) := LinearEquiv.ofBijective (Matrix.mulVecLin T) ⟨hi, hs⟩
  simpa using e.finrank_eq.symm

theorem eq_zero_of_mulVec_eq_zero_of_commute {Y : Set (Matrix (Fin r) (Fin r) F)}
    (hY : ∀ W : Submodule F (Fin r → F), (∀ y ∈ Y, ∀ w ∈ W, y.mulVec w ∈ W) → W = ⊥ ∨ W = ⊤)
    {B : Matrix (Fin r) (Fin r) F} (hB : ∀ y ∈ Y, B * y = y * B) (hB0 : B ≠ 0)
    {w : Fin r → F} (hw : B.mulVec w = 0) : w = 0 := by
  let W : Submodule F (Fin r → F) := LinearMap.ker (Matrix.mulVecLin B)
  have hW : ∀ y ∈ Y, ∀ w ∈ W, y.mulVec w ∈ W := by
    intro y hy w hw
    show B.mulVec (y.mulVec w) = 0
    have h : B.mulVec (y.mulVec w) = y.mulVec (B.mulVec w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB y hy]
    have h0 : B.mulVec w = 0 := hw
    rw [h, h0, Matrix.mulVec_zero]
  rcases hY W hW with h | h
  · have hw' : w ∈ W := hw
    rw [h, Submodule.mem_bot] at hw'
    exact hw'
  · exfalso
    apply hB0
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have hv : v ∈ W := by rw [h]; trivial
    rw [Matrix.zero_mulVec]
    exact hv

theorem exists_scalar_of_pow_card_eq [Fintype F] (hr : 0 < r)
    {Y : Set (Matrix (Fin r) (Fin r) F)}
    (hY : ∀ W : Submodule F (Fin r → F), (∀ y ∈ Y, ∀ w ∈ W, y.mulVec w ∈ W) → W = ⊥ ∨ W = ⊤)
    {T : Matrix (Fin r) (Fin r) F} (hT : ∀ y ∈ Y, T * y = y * T)
    (hq : T ^ Fintype.card F = T) :
    ∃ a : F, T = Matrix.scalar (Fin r) a := by
  classical
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have halg : ∀ b : F, algebraMap F (Matrix (Fin r) (Fin r) F) b = Matrix.scalar (Fin r) b :=
    fun b => rfl
  have hfac : (∏ a : F, (Polynomial.X - Polynomial.C a) : Polynomial F) =
      Polynomial.X ^ Fintype.card F - Polynomial.X := by
    have hmonic : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial F).Monic := by
      refine Polynomial.monic_X_pow_sub ?_
      rw [Polynomial.degree_X]
      exact_mod_cast Fintype.one_lt_card
    have hroots : Multiset.card
        (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial F).roots =
        (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial F).natDegree := by
      rw [FiniteField.roots_X_pow_card_sub_X, FiniteField.X_pow_card_sub_X_natDegree_eq F
        Fintype.one_lt_card]
      exact Finset.card_univ
    have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hroots
    rw [FiniteField.roots_X_pow_card_sub_X] at this
    exact this
  have key : ∀ s : Finset F, Polynomial.aeval T (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) = 0 →
      ∃ a ∈ s, T = Matrix.scalar (Fin r) a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h
      simp at h
    | insert b s hb ih =>
      intro h
      rw [Finset.prod_insert hb, map_mul] at h
      by_cases hTb : T - Matrix.scalar (Fin r) b = 0
      · exact ⟨b, Finset.mem_insert_self b s, sub_eq_zero.mp hTb⟩
      · have hcomm : ∀ y ∈ Y, (T - Matrix.scalar (Fin r) b) * y =
            y * (T - Matrix.scalar (Fin r) b) := by
          intro y hy
          rw [Matrix.sub_mul, Matrix.mul_sub, hT y hy,
            (Matrix.scalar_commute b (fun _ => Commute.all _ _) y).eq]
        have hZ : Polynomial.aeval T (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) = 0 := by
          refine Matrix.ext_iff_mulVec.mpr fun w => ?_
          rw [Matrix.zero_mulVec]
          refine eq_zero_of_mulVec_eq_zero_of_commute hY hcomm hTb ?_
          rw [Matrix.mulVec_mulVec]
          have : (T - Matrix.scalar (Fin r) b) * Polynomial.aeval T
              (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) = 0 := by
            simpa [Polynomial.aeval_X, Polynomial.aeval_C, halg] using h
          rw [this, Matrix.zero_mulVec]
        obtain ⟨a, ha, hTa⟩ := ih hZ
        exact ⟨a, Finset.mem_insert_of_mem ha, hTa⟩
  obtain ⟨a, -, ha⟩ := key Finset.univ (by rw [hfac]; simp [hq])
  exact ⟨a, ha⟩

theorem exists_ringEquiv_of_scalar [Finite F] (hr : 0 < r)
    (φ : F →+* Matrix (Fin r) (Fin r) F) (hφ : ∀ c, ∃ a : F, φ c = Matrix.scalar (Fin r) a) :
    ∃ ϑ : F ≃+* F, ∀ c, φ c = Matrix.scalar (Fin r) (ϑ c) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hsc : Function.Injective (Matrix.scalar (Fin r) : F →+* Matrix (Fin r) (Fin r) F) :=
    fun a b h => Matrix.scalar_inj.mp h
  choose ϑ₀ hϑ₀ using hφ
  let ϑ : F →+* F :=
    { toFun := ϑ₀
      map_one' := hsc (by rw [← hϑ₀, map_one, map_one])
      map_mul' := fun a b => hsc (by rw [← hϑ₀, map_mul, hϑ₀, hϑ₀, map_mul])
      map_zero' := hsc (by rw [← hϑ₀, map_zero, map_zero])
      map_add' := fun a b => hsc (by rw [← hϑ₀, map_add, hϑ₀, hϑ₀, map_add]) }
  have hinj : Function.Injective ϑ := fun a b h =>
    φ.injective (by rw [hϑ₀, hϑ₀]; exact congrArg _ h)
  exact ⟨RingEquiv.ofBijective ϑ (Finite.injective_iff_bijective.mp hinj), hϑ₀⟩

@[expose] def untwist (γ : Matrix (Fin d) (Fin d) F →+* Matrix (Fin r) (Fin r) F) (ϑ : F ≃+* F) :
    Matrix (Fin d) (Fin d) F →+* Matrix (Fin r) (Fin r) F :=
  γ.comp (RingEquiv.mapMatrix (m := Fin d) ϑ.symm).toRingHom

theorem untwist_apply (γ : Matrix (Fin d) (Fin d) F →+* Matrix (Fin r) (Fin r) F) (ϑ : F ≃+* F)
    (A : Matrix (Fin d) (Fin d) F) : untwist γ ϑ A = γ (A.map ϑ.symm) := rfl

theorem untwist_map_apply (γ : Matrix (Fin d) (Fin d) F →+* Matrix (Fin r) (Fin r) F)
    (ϑ : F ≃+* F) (A : Matrix (Fin d) (Fin d) F) : untwist γ ϑ (A.map ϑ) = γ A := by
  rw [untwist_apply]
  congr 1
  ext i j
  simp

theorem untwist_injective {γ : Matrix (Fin d) (Fin d) F →+* Matrix (Fin r) (Fin r) F}
    (hγ : Function.Injective γ) (ϑ : F ≃+* F) : Function.Injective (untwist γ ϑ) :=
  hγ.comp (RingEquiv.mapMatrix (m := Fin d) ϑ.symm).injective

theorem untwist_smul (γ : Matrix (Fin d) (Fin d) F →+* Matrix (Fin r) (Fin r) F) (ϑ : F ≃+* F)
    (hϑ : ∀ c, γ (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin r) (ϑ c)) (c : F)
    (A : Matrix (Fin d) (Fin d) F) : untwist γ ϑ (c • A) = c • untwist γ ϑ A := by
  have h1 : c • A = Matrix.scalar (Fin d) c * A := by
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have h2 : untwist γ ϑ (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin r) c := by
    rw [untwist_apply]
    have : (Matrix.scalar (Fin d) c).map ϑ.symm = Matrix.scalar (Fin d) (ϑ.symm c) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
    rw [this, hϑ, RingEquiv.apply_symm_apply]
  rw [h1, map_mul, h2, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem exists_conj_of_ringHom [Finite F] (hd : 0 < d)
    (α : Matrix (Fin d) (Fin d) F →+* Matrix (Fin d) (Fin d) F) (hα : Function.Injective α) :
    ∃ (ϑ : F ≃+* F) (T : Matrix (Fin d) (Fin d) F), IsUnit T ∧
      ∀ A, α A = T * A.map ϑ * T⁻¹ := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hsurj : Function.Surjective α := Finite.injective_iff_surjective.mp hα
  have hcent : ∀ c : F, ∃ a : F, (α.comp (Matrix.scalar (Fin d))) c = Matrix.scalar (Fin d) a := by
    intro c
    have hmem : α (Matrix.scalar (Fin d) c) ∈ Set.range (Matrix.scalar (Fin d)) := by
      rw [Matrix.mem_range_scalar_iff_commute_single']
      intro i j
      obtain ⟨A, hA⟩ := hsurj (Matrix.single i j 1)
      rw [← hA]
      have hc : Commute A (Matrix.scalar (Fin d) c) :=
        (Matrix.scalar_commute c (fun _ => Commute.all _ _) A).symm
      exact hc.map α
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha.symm⟩
  obtain ⟨ϑ, hϑ⟩ := exists_ringEquiv_of_scalar hd (α.comp (Matrix.scalar (Fin d))) hcent
  obtain ⟨T, hTi, hT⟩ := exists_matrix_intertwiner hd (untwist α ϑ) (untwist_smul α ϑ hϑ)
    (untwist_injective hα ϑ)
  have hTu : IsUnit T := Matrix.mulVec_injective_iff_isUnit.mp hTi
  refine ⟨ϑ, T, hTu, fun A => ?_⟩
  have h := eq_mul_mul_inv_of_mul_eq hTu (hT (A.map ϑ))
  rwa [untwist_map_apply] at h

theorem exists_conj_of_ringEquiv [Finite F] (hd : 0 < d)
    (α : Matrix (Fin d) (Fin d) F ≃+* Matrix (Fin d) (Fin d) F) :
    ∃ (ϑ : F ≃+* F) (T : Matrix (Fin d) (Fin d) F), IsUnit T ∧
      ∀ A, α A = T * A.map ϑ * T⁻¹ :=
  exists_conj_of_ringHom hd α.toRingHom α.injective

end CFSG.Quasithin.SwapModel

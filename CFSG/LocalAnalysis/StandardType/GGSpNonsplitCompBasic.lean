module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneRestSp

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank Matrix
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

namespace SpNonsplitComp

variable {F : Type} [Field F] {n e s r p : ℕ}

@[expose] def bdHom :
    (Fin s → Matrix (Fin e) (Fin e) F) × Matrix (Fin r) (Fin r) F →+*
      Matrix ((Fin e × Fin s) ⊕ Fin r) ((Fin e × Fin s) ⊕ Fin r) F where
  toFun x := fromBlocks (blockDiagonal x.1) 0 0 x.2
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one]
    rw [blockDiagonal_one, fromBlocks_one]
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [fromBlocks_multiply, Pi.mul_def, blockDiagonal_mul]
    simp
  map_zero' := by
    simp only [Prod.fst_zero, Prod.snd_zero]
    rw [blockDiagonal_zero, fromBlocks_zero]
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add]
    rw [fromBlocks_add, blockDiagonal_add]
    simp

theorem bdHom_apply (x : (Fin s → Matrix (Fin e) (Fin e) F) × Matrix (Fin r) (Fin r) F) :
    bdHom x = fromBlocks (blockDiagonal x.1) 0 0 x.2 :=
  rfl

theorem nsCore_eq_bdHom (C : Matrix (Fin e) (Fin e) F) (k : Fin s → ℕ) :
    SLNS.nsCore (r := r) C k = bdHom (fun j => C ^ k j, 1) :=
  rfl

@[expose] noncomputable def frameRing (A₀ : GL (Fin n ⊕ Fin n) F)
    (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) :
    Matrix ((Fin e × Fin s) ⊕ Fin r) ((Fin e × Fin s) ⊕ Fin r) F →+*
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F where
  toFun N := (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * N.submatrix ε ε *
    ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  map_one' := by
    rw [submatrix_one_equiv, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  map_mul' N N' := by
    have hA : ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [← submatrix_mul_equiv N N' ε ε ε]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F),
      hA, Matrix.one_mul]
  map_zero' := by simp
  map_add' N N' := by
    have h : (N + N').submatrix ε ε = N.submatrix ε ε + N'.submatrix ε ε := by
      ext a b
      simp
    rw [h, Matrix.mul_add, Matrix.add_mul]

theorem frameRing_apply (A₀ : GL (Fin n ⊕ Fin n) F) (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    (N : Matrix ((Fin e × Fin s) ⊕ Fin r) ((Fin e × Fin s) ⊕ Fin r) F) :
    frameRing A₀ ε N = (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * N.submatrix ε ε *
      ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
  rfl

theorem inv_mul_frameRing_mul (A₀ : GL (Fin n ⊕ Fin n) F)
    (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    (N : Matrix ((Fin e × Fin s) ⊕ Fin r) ((Fin e × Fin s) ⊕ Fin r) F) :
    ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      frameRing A₀ ε N * (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = N.submatrix ε ε := by
  have hA : ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [frameRing_apply]
  simp only [Matrix.mul_assoc, hA, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hA, Matrix.one_mul]

theorem frameRing_injective (A₀ : GL (Fin n ⊕ Fin n) F)
    (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) : Function.Injective (frameRing A₀ ε) := by
  intro N N' h
  have h1 : N.submatrix ε ε = N'.submatrix ε ε := by
    rw [← inv_mul_frameRing_mul A₀ ε N, ← inv_mul_frameRing_mul A₀ ε N', h]
  have h2 := congrArg (fun M => M.submatrix ε.symm ε.symm) h1
  simpa only [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] using h2

theorem mat_eq_of_spBlockMat {A₀ : GL (Fin n ⊕ Fin n) F}
    {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {C : Matrix (Fin e) (Fin e) F}
    {X : StatedSp n F} {k : Fin s → ℕ} (hX : RootPlaneSp.SpBlockMat A₀ ε C X k) :
    mat n F X = frameRing A₀ ε (SLNS.nsCore C k) :=
  hX

@[expose] def truncExp (p : ℕ) (k k' : Fin s → ℕ) : Fin s → ℕ :=
  fun j => if p ∣ k j then k' j else 0

theorem pow_eq_one_of_dvd {C : Matrix (Fin e) (Fin e) F} (hCp : C ^ p = 1) {j : ℕ} (hj : p ∣ j) :
    C ^ j = 1 := by
  obtain ⟨m, rfl⟩ := hj
  rw [pow_mul, hCp, one_pow]

theorem geom_sum_eq_zero {C : Matrix (Fin e) (Fin e) F} (hCp : C ^ p = 1)
    (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) {j : ℕ} (hj : ¬ p ∣ j) :
    ∑ i ∈ Finset.range p, (C ^ j) ^ i = 0 := by
  have h1 := geom_sum_mul (C ^ j) p
  have h2 : (C ^ j) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hCp, one_pow]
  rw [h2, sub_self] at h1
  have hu := hcunit j hj 1
  rw [one_smul] at hu
  exact hu.mul_left_eq_zero.mp h1

theorem natCast_eq_one [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) : (p : F) = 1 := by
  rw [CharP.cast_eq_mod F 2 p, Nat.odd_iff.mp (hp.odd_of_ne_two hp2), Nat.cast_one]

theorem sum_range_one_pow [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ i ∈ Finset.range p, (1 : Matrix (Fin e) (Fin e) F) ^ i = 1 := by
  simp only [one_pow, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul F, natCast_eq_one hp hp2, one_smul]

theorem nsCore_truncExp [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) {C : Matrix (Fin e) (Fin e) F}
    (hCp : C ^ p = 1) (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1))
    (k k' : Fin s → ℕ) :
    SLNS.nsCore (r := r) C (truncExp p k k') =
      SLNS.nsCore C k' * (∑ i ∈ Finset.range p, SLNS.nsCore C k ^ i) + 1 -
        ∑ i ∈ Finset.range p, SLNS.nsCore C k ^ i := by
  have key : ((fun j => C ^ truncExp p k k' j, 1) :
      (Fin s → Matrix (Fin e) (Fin e) F) × Matrix (Fin r) (Fin r) F) =
      (fun j => C ^ k' j, 1) * (∑ i ∈ Finset.range p, (fun j => C ^ k j, 1) ^ i) + 1 -
        ∑ i ∈ Finset.range p, ((fun j => C ^ k j, 1) :
          (Fin s → Matrix (Fin e) (Fin e) F) × Matrix (Fin r) (Fin r) F) ^ i := by
    refine Prod.ext ?_ ?_
    · funext j
      simp only [Prod.fst_sub, Prod.fst_add, Prod.fst_mul, Prod.fst_one, Prod.fst_sum,
        Prod.pow_fst, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.one_apply, Finset.sum_apply,
        Pi.pow_apply]
      unfold truncExp
      split_ifs with hj
      · rw [pow_eq_one_of_dvd hCp hj, sum_range_one_pow hp hp2, mul_one, add_sub_cancel_right]
      · rw [geom_sum_eq_zero hCp hcunit hj, mul_zero, zero_add, sub_zero, pow_zero]
    · simp only [Prod.snd_sub, Prod.snd_add, Prod.snd_mul, Prod.snd_one, Prod.snd_sum,
        Prod.pow_snd]
      rw [one_mul, add_sub_cancel_left]
  have h := congrArg bdHom key
  rw [map_sub, map_add, map_mul, map_one, map_sum] at h
  simp only [map_pow] at h
  simp only [nsCore_eq_bdHom]
  exact h

theorem nsCore_truncExp_mul_sub_one {C : Matrix (Fin e) (Fin e) F} (hCp : C ^ p = 1)
    (k k' : Fin s → ℕ) :
    SLNS.nsCore (r := r) C (truncExp p k k') * (SLNS.nsCore C k - 1) = SLNS.nsCore C k - 1 := by
  have key : ((fun j => C ^ truncExp p k k' j, 1) :
      (Fin s → Matrix (Fin e) (Fin e) F) × Matrix (Fin r) (Fin r) F) *
        ((fun j => C ^ k j, 1) - 1) = (fun j => C ^ k j, 1) - 1 := by
    refine Prod.ext ?_ ?_
    · funext j
      simp only [Prod.fst_mul, Prod.fst_sub, Prod.fst_one, Pi.mul_apply, Pi.sub_apply,
        Pi.one_apply]
      unfold truncExp
      split_ifs with hj
      · rw [pow_eq_one_of_dvd hCp hj, sub_self, mul_zero]
      · rw [pow_zero, one_mul]
    · simp only [Prod.snd_mul, Prod.snd_sub, Prod.snd_one]
      rw [one_mul]
  have h := congrArg bdHom key
  rw [map_mul, map_sub, map_one] at h
  simp only [nsCore_eq_bdHom]
  exact h

theorem nsCore_pow_p {C : Matrix (Fin e) (Fin e) F} (hCp : C ^ p = 1) (k : Fin s → ℕ) :
    SLNS.nsCore (r := r) C k ^ p = 1 := by
  have key : ((fun j => C ^ k j, 1) :
      (Fin s → Matrix (Fin e) (Fin e) F) × Matrix (Fin r) (Fin r) F) ^ p = 1 := by
    refine Prod.ext ?_ ?_
    · funext j
      simp only [Prod.pow_fst, Pi.pow_apply, Prod.fst_one, Pi.one_apply]
      rw [← pow_mul, mul_comm, pow_mul, hCp, one_pow]
    · simp
  have h := congrArg bdHom key
  rw [map_pow, map_one] at h
  rw [nsCore_eq_bdHom]
  exact h

section Frame

variable {A₀ : GL (Fin n ⊕ Fin n) F} {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r}
  {C : Matrix (Fin e) (Fin e) F}

theorem pow_p_eq_one (hCp : C ^ p = 1) {X : StatedSp n F} {k : Fin s → ℕ}
    (hX : RootPlaneSp.SpBlockMat A₀ ε C X k) : X ^ p = 1 := by
  apply mat_injective
  rw [map_pow, map_one, mat_eq_of_spBlockMat hX, ← map_pow, nsCore_pow_p hCp, map_one]

theorem commute_of_spBlockMat {X Y : StatedSp n F} {k k' : Fin s → ℕ}
    (hX : RootPlaneSp.SpBlockMat A₀ ε C X k) (hY : RootPlaneSp.SpBlockMat A₀ ε C Y k') :
    X * Y = Y * X := by
  apply mat_injective
  rw [map_mul, map_mul, mat_eq_of_spBlockMat hX, mat_eq_of_spBlockMat hY, ← map_mul, ← map_mul,
    SLNS.nsCore_mul, SLNS.nsCore_mul, add_comm]

theorem four_le_finrank_of_fix (he : 2 ≤ e) (hs : 4 ≤ s) {X : StatedSp n F} {k : Fin s → ℕ}
    (hX : RootPlaneSp.SpBlockMat A₀ ε C X k) (hk : RootPlaneSp.PlaneSupp k)
    {W : Submodule F (Fin n ⊕ Fin n → F)} (hW : ∀ v, mat n F X *ᵥ v = v → v ∈ W) :
    4 ≤ Module.finrank F W := by
  classical
  let idx : Fin 2 × Fin 2 → Fin n ⊕ Fin n := fun t =>
    ε.symm (Sum.inl ((⟨t.1, by omega⟩ : Fin e), (⟨t.2 + 2, by omega⟩ : Fin s)))
  have hidx : Function.Injective idx := by
    intro t t' h
    have h1 := ε.symm.injective h
    simp only [Sum.inl.injEq, Prod.mk.injEq, Fin.mk.injEq] at h1
    exact Prod.ext (Fin.ext h1.1) (Fin.ext (by omega))
  let w : Fin 2 × Fin 2 → (Fin n ⊕ Fin n → F) := fun t =>
    (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ Pi.single (idx t) 1
  have hli : LinearIndependent F w := by
    have h1 : LinearIndependent F
        (fun t => (Pi.single (idx t) (1 : F) : Fin n ⊕ Fin n → F)) := by
      have := (Pi.basisFun F (Fin n ⊕ Fin n)).linearIndependent.comp idx hidx
      simpa only [Function.comp_def, Pi.basisFun_apply] using this
    have hker : LinearMap.ker
        (Matrix.mulVecLin (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) = ⊥ := by
      rw [Matrix.ker_mulVecLin_eq_bot_iff]
      intro v hv
      have h2 := congrArg (fun z => ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ z) hv
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
      rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
    have h3 := h1.map' _ hker
    have hw : w = (Matrix.mulVecLin (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) ∘
        fun t => (Pi.single (idx t) (1 : F) : Fin n ⊕ Fin n → F) := by
      funext t
      simp only [w, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [hw]
    exact h3
  have hspan : Submodule.span F (Set.range w) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    apply hW
    have h2 : 2 ≤ ((⟨t.2 + 2, by omega⟩ : Fin s) : ℕ) := Nat.le_add_left 2 _
    exact RootPlaneSp.fix_of_zero hX (hk _ h2) _
  calc 4 = Fintype.card (Fin 2 × Fin 2) := by simp
    _ = Module.finrank F (Submodule.span F (Set.range w)) := (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank F W := Submodule.finrank_mono hspan

end Frame

end SpNonsplitComp

end CFSG.StandardType

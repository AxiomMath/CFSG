module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3Contracts

public section

namespace S2MathAs3_1624

noncomputable section

open scoped MatrixGroups Matrix

private noncomputable def ltrd3j2_mulVecEquiv {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A : (Matrix n n R)ˣ) : (n → R) ≃ₗ[R] (n → R) where
  toFun v := (A : Matrix n n R) *ᵥ v
  invFun v := ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) *ᵥ v
  map_add' v w := by rw [Matrix.mulVec_add]
  map_smul' c v := by rw [Matrix.mulVec_smul]; rfl
  left_inv v := by
    show ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) *ᵥ ((A : Matrix n n R) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec]
    have h : ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) * (A : Matrix n n R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [h, Matrix.one_mulVec]
  right_inv v := by
    show (A : Matrix n n R) *ᵥ (((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec]
    have h : (A : Matrix n n R) * ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h, Matrix.one_mulVec]

@[simp] private theorem ltrd3j2_mulVecEquiv_apply {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A : (Matrix n n R)ˣ) (v : n → R) :
    ltrd3j2_mulVecEquiv A v = (A : Matrix n n R) *ᵥ v := rfl

private theorem ltrd3j2_mulVecEquiv_mul_apply {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A B : (Matrix n n R)ˣ) (v : n → R) :
    ltrd3j2_mulVecEquiv (A * B) v = ltrd3j2_mulVecEquiv A (ltrd3j2_mulVecEquiv B v) := by
  simp only [ltrd3j2_mulVecEquiv_apply, Units.val_mul, Matrix.mulVec_mulVec]

private theorem ltrd3j2_matrix_eq_of_mulVec {n R : Type} [Field R] [Fintype n]
    {M N : Matrix n n R} (h : ∀ v : n → R, M *ᵥ v = N *ᵥ v) : M = N :=
  Matrix.ext_iff_mulVec.mpr h

private noncomputable def ltrd3j2_matrixUnit {R : Type} [Field R] {n : ℕ}
    (e : (Fin n → R) ≃ₗ[R] (Fin n → R)) : (Matrix (Fin n) (Fin n) R)ˣ :=
  let toMat : ((Fin n → R) →ₗ[R] (Fin n → R)) ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
    LinearMap.toMatrixAlgEquiv'
  ⟨toMat e.toLinearMap, toMat e.symm.toLinearMap, by
     show toMat.toMulEquiv e.toLinearMap * toMat.toMulEquiv e.symm.toLinearMap = 1
     rw [← toMat.toMulEquiv.map_mul, ← toMat.toMulEquiv.map_one]
     congr 1
     ext x
     simp, by
     show toMat.toMulEquiv e.symm.toLinearMap * toMat.toMulEquiv e.toLinearMap = 1
     rw [← toMat.toMulEquiv.map_mul, ← toMat.toMulEquiv.map_one]
     congr 1
     ext x
     simp⟩

private theorem ltrd3j2_matrixUnit_mulVec {R : Type} [Field R] {n : ℕ}
    (e : (Fin n → R) ≃ₗ[R] (Fin n → R)) (x : Fin n → R) :
    ((ltrd3j2_matrixUnit e : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) *ᵥ x
      = e x := by
  show LinearMap.toMatrixAlgEquiv' e.toLinearMap *ᵥ x = e x
  rw [← Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  rfl

private theorem ltrd3j2_adjoin_eq_top {K E : Type} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] (hfin : Module.finrank K E = 3) (κ : Kˣ) (α : E)
    (hα : α ^ 3 = algebraMap K E (κ : K)) (hκ : ∀ c : K, c ^ 3 ≠ (κ : K)) :
    Algebra.adjoin K ({α} : Set E) = ⊤ := by
  have hp : Irreducible (Polynomial.X ^ 3 - Polynomial.C (κ : K)) :=
    X_pow_sub_C_irreducible_of_prime (by norm_num) hκ
  have hroot : Polynomial.aeval α (Polynomial.X ^ 3 - Polynomial.C (κ : K)) = 0 := by
    simp [hα]
  have hmin : Polynomial.X ^ 3 - Polynomial.C (κ : K) = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic hp hroot (Polynomial.monic_X_pow_sub_C (κ : K) (by norm_num))
  have hdeg : (minpoly K α).natDegree = 3 := by
    rw [← hmin, Polynomial.natDegree_X_pow_sub_C]
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hdim : Module.finrank K (Algebra.adjoin K ({α} : Set E)) = 3 := by
    rw [(Algebra.adjoin.powerBasis' hint).finrank, Algebra.adjoin.powerBasis'_dim hint, hdeg]
  have htop_fin : Module.finrank K (⊤ : Subalgebra K E) = 3 := by
    rw [subalgebra_top_finrank_eq_submodule_top_finrank, finrank_top, hfin]
  exact Subalgebra.eq_of_le_of_finrank_le le_top (by rw [htop_fin, hdim])

private theorem ltrd3j2_smul_mem_adjoin {K E : Type} [Field K] [Field E] [Algebra K E]
    {m : ℕ} (α : E) (hgen : Algebra.adjoin K ({α} : Set E) = ⊤)
    (T : (Fin m → E) →ₗ[K] (Fin m → E)) (hα : ∀ w, T (α • w) = α • T w)
    (c : E) (hc : c ∈ Algebra.adjoin K ({α} : Set E)) (w : Fin m → E) :
    T (c • w) = c • T w := by
  exact Algebra.adjoin_induction (R := K)
    (p := fun c _ => ∀ v : Fin m → E, T (c • v) = c • T v)
    (fun x hx v => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hα v)
    (fun k v => by
      rw [IsScalarTower.algebraMap_smul E k v, T.map_smul,
        IsScalarTower.algebraMap_smul E k (T v)])
    (fun x y hx hy hx' hy' v => by
      rw [add_smul, T.map_add, hx' v, hy' v, add_smul])
    (fun x y hx hy hx' hy' v => by
      rw [mul_smul, hx' (y • v), hy' v, mul_smul])
    hc w

private noncomputable def ltrd3j2_linearEquivE {K E : Type} [Field K] [Field E] [Algebra K E]
    {m : ℕ} (α : E) (hgen : Algebra.adjoin K ({α} : Set E) = ⊤)
    (f : (Fin m → E) ≃ₗ[K] (Fin m → E)) (hf : ∀ w, f (α • w) = α • f w) :
    (Fin m → E) ≃ₗ[E] (Fin m → E) where
  toFun := f
  invFun := f.symm
  map_add' := f.map_add
  map_smul' c w := ltrd3j2_smul_mem_adjoin α hgen f.toLinearMap hf c (by rw [hgen]; trivial) w
  left_inv := f.left_inv
  right_inv := f.right_inv

theorem linearFullCentralizer_holds : LinearFullCentralizerContract := by
  intro K hKf hKfin hKchar d hd S κ hκ hS3 m E hEf hEalg hEfin hd3 hcubic α hα b hbS
  let : FiniteDimensional K E := hcubic.1
  have hfin3 : Module.finrank K E = 3 := hcubic.2.1
  have hκfield : ∀ c : K, c ^ 3 ≠ (κ : K) := (noncube_units_iff_field κ).mp hκ
  have hgen : Algebra.adjoin K ({α} : Set E) = ⊤ :=
    ltrd3j2_adjoin_eq_top hfin3 κ α hα hκfield
  have hSb : ∀ w : Fin m → E,
      b ((S : Matrix (Fin d) (Fin d) K) *ᵥ b.symm w) = α • w := by
    intro w
    rw [hbS (b.symm w), LinearEquiv.apply_symm_apply]
  have hmem : ∀ g : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K))),
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (S : Matrix (Fin d) (Fin d) K)
        = (S : Matrix (Fin d) (Fin d) K)
            * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro g
    have hg : (g : GL (Fin d) K) * S = S * (g : GL (Fin d) K) :=
      ((Subgroup.mem_centralizer_iff.mp g.2) S (Set.mem_singleton S)).symm
    have := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) hg
    simpa using this
  let gU : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K)))
      → (Matrix (Fin d) (Fin d) K)ˣ := fun g => (g : GL (Fin d) K)
  let gL : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K)))
      → (Fin d → K) ≃ₗ[K] (Fin d → K) := fun g => ltrd3j2_mulVecEquiv (gU g)
  let fg : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K)))
      → (Fin m → E) ≃ₗ[K] (Fin m → E) := fun g => b.symm.trans ((gL g).trans b)
  have hfg : ∀ g : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K))),
      ∀ w : Fin m → E, fg g (α • w) = α • fg g w := by
    intro g w
    have hgS : ∀ v : Fin d → K,
        (gU g) *ᵥ ((S : Matrix (Fin d) (Fin d) K) *ᵥ v)
          = (S : Matrix (Fin d) (Fin d) K) *ᵥ ((gU g) *ᵥ v) := by
      intro v
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmem g]
    have h1 : b.symm (α • w) = (S : Matrix (Fin d) (Fin d) K) *ᵥ b.symm w := by
      rw [← hSb w, LinearEquiv.symm_apply_apply]
    show b ((gL g) (b.symm (α • w))) = α • b ((gL g) (b.symm w))
    rw [h1]
    have h2 : (gL g) ((S : Matrix (Fin d) (Fin d) K) *ᵥ b.symm w)
        = (S : Matrix (Fin d) (Fin d) K) *ᵥ ((gL g) (b.symm w)) := by
      simpa [gL, ltrd3j2_mulVecEquiv_apply] using hgS (b.symm w)
    rw [h2]
    have h3 := hSb (b ((gL g) (b.symm w)))
    rwa [LinearEquiv.symm_apply_apply] at h3
  let eg : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K)))
      → (Fin m → E) ≃ₗ[E] (Fin m → E) :=
    fun g => ltrd3j2_linearEquivE α hgen (fg g) (hfg g)
  let Φfun : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K)))
      → (Matrix (Fin m) (Fin m) E)ˣ := fun g => ltrd3j2_matrixUnit (eg g)
  have hmul : ∀ g h : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K))),
      Φfun (g * h) = Φfun g * Φfun h := by
    intro g h
    apply Units.ext
    show LinearMap.toMatrixAlgEquiv' (eg (g * h)).toLinearMap
        = LinearMap.toMatrixAlgEquiv' (eg g).toLinearMap
          * LinearMap.toMatrixAlgEquiv' (eg h).toLinearMap
    rw [← map_mul]
    congr 1
    apply LinearMap.ext
    intro w
    show (fg (g * h)) w = (fg g) ((fg h) w)
    show b ((gL (g * h)) (b.symm w)) = b ((gL g) (b.symm (b ((gL h) (b.symm w)))))
    rw [LinearEquiv.symm_apply_apply]
    congr 1
    have hcomp : (gL (g * h)) (b.symm w) = (gL g) ((gL h) (b.symm w)) := by
      show ltrd3j2_mulVecEquiv (gU (g * h)) (b.symm w)
          = ltrd3j2_mulVecEquiv (gU g) (ltrd3j2_mulVecEquiv (gU h) (b.symm w))
      rw [show gU (g * h) = gU g * gU h from rfl]
      exact ltrd3j2_mulVecEquiv_mul_apply (gU g) (gU h) (b.symm w)
    rw [hcomp]
  have hone : Φfun 1 = 1 := by
    apply Units.ext
    show LinearMap.toMatrixAlgEquiv' (eg 1).toLinearMap = 1
    rw [← map_one (f := LinearMap.toMatrixAlgEquiv' (R := E) (n := Fin m))]
    congr 1
    apply LinearMap.ext
    intro w
    show (fg 1) w = w
    show b ((gL 1) (b.symm w)) = w
    have h1 : gL 1 = LinearEquiv.refl K (Fin d → K) := by
      apply LinearEquiv.ext
      intro x
      show ltrd3j2_mulVecEquiv (gU 1) x = x
      rw [show gU 1 = 1 from rfl, ltrd3j2_mulVecEquiv_apply, Units.val_one, Matrix.one_mulVec]
    rw [h1]
    simp
  let Φhom : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K))) →* GL (Fin m) E :=
    { toFun := Φfun, map_one' := hone, map_mul' := hmul }
  have hinj : Function.Injective Φfun := by
    intro g h hgh
    have hmat : ((Φfun g : (Matrix (Fin m) (Fin m) E)ˣ) : Matrix (Fin m) (Fin m) E)
        = ((Φfun h : (Matrix (Fin m) (Fin m) E)ˣ) : Matrix (Fin m) (Fin m) E) := by
      rw [hgh]
    have hlin : (eg g).toLinearMap = (eg h).toLinearMap := by
      have h1 : Matrix.toLinAlgEquiv'
          ((Φfun g : (Matrix (Fin m) (Fin m) E)ˣ) : Matrix (Fin m) (Fin m) E)
          = (eg g).toLinearMap := by
        show Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (eg g).toLinearMap)
            = (eg g).toLinearMap
        rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
      have h2 : Matrix.toLinAlgEquiv'
          ((Φfun h : (Matrix (Fin m) (Fin m) E)ˣ) : Matrix (Fin m) (Fin m) E)
          = (eg h).toLinearMap := by
        show Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (eg h).toLinearMap)
            = (eg h).toLinearMap
        rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
      have hcong := congrArg Matrix.toLinAlgEquiv' hmat
      rw [h1, h2] at hcong
      exact hcong
    have hfun : ∀ w : Fin m → E, fg g w = fg h w := fun w => LinearMap.congr_fun hlin w
    have hgl : gL g = gL h := by
      apply LinearEquiv.ext
      intro x
      have hb : b ((gL g) x) = b ((gL h) x) := by
        have := hfun (b x)
        simpa [fg, LinearEquiv.symm_apply_apply] using this
      exact b.injective hb
    have hU : gU g = gU h := by
      apply Units.ext
      apply ltrd3j2_matrix_eq_of_mulVec
      intro v
      have := congrArg (fun e : (Fin d → K) ≃ₗ[K] (Fin d → K) => e v) hgl
      simpa [gL, ltrd3j2_mulVecEquiv_apply] using this
    exact Subtype.ext hU
  have hsurj : Function.Surjective Φfun := by
    intro A
    let eA : (Fin m → E) ≃ₗ[E] (Fin m → E) := ltrd3j2_mulVecEquiv A
    let hA : (Fin d → K) ≃ₗ[K] (Fin d → K) := b.trans ((eA.restrictScalars K).trans b.symm)
    have hA_S : ∀ v : Fin d → K, hA ((S : Matrix (Fin d) (Fin d) K) *ᵥ v)
        = (S : Matrix (Fin d) (Fin d) K) *ᵥ hA v := by
      intro v
      have h2 : hA ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = b.symm (eA (α • b v)) := by
        show b.symm ((eA.restrictScalars K) (b ((S : Matrix (Fin d) (Fin d) K) *ᵥ v)))
            = b.symm (eA (α • b v))
        rw [hbS v, LinearEquiv.restrictScalars_apply]
      rw [h2]
      have h3 : eA (α • b v) = α • eA (b v) := map_smul eA α (b v)
      rw [h3]
      have h4 : b.symm (α • eA (b v))
          = (S : Matrix (Fin d) (Fin d) K) *ᵥ b.symm (eA (b v)) := by
        rw [← hSb (eA (b v)), LinearEquiv.symm_apply_apply]
      rw [h4]
      rfl
    let gA : (Matrix (Fin d) (Fin d) K)ˣ := ltrd3j2_matrixUnit hA
    have hgA_mulVec : ∀ v : Fin d → K, (gA : Matrix (Fin d) (Fin d) K) *ᵥ v = hA v := by
      intro v
      simpa [gA] using ltrd3j2_matrixUnit_mulVec hA v
    have hcommA : gA * S = S * gA := by
      apply Units.ext
      apply ltrd3j2_matrix_eq_of_mulVec
      intro v
      show (↑(gA * S) : Matrix (Fin d) (Fin d) K) *ᵥ v
          = (↑(S * gA) : Matrix (Fin d) (Fin d) K) *ᵥ v
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      simp only [hgA_mulVec]
      exact hA_S v
    have hmemA : gA ∈ Subgroup.centralizer ({S} : Set (GL (Fin d) K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcommA.symm
    refine ⟨⟨gA, hmemA⟩, ?_⟩
    have hfgA : ∀ w : Fin m → E, (eg ⟨gA, hmemA⟩) w = eA w := by
      intro w
      show b ((gL ⟨gA, hmemA⟩) (b.symm w)) = eA w
      have h1 : (gL ⟨gA, hmemA⟩) (b.symm w) = hA (b.symm w) := by
        show ltrd3j2_mulVecEquiv (gU ⟨gA, hmemA⟩) (b.symm w) = hA (b.symm w)
        rw [ltrd3j2_mulVecEquiv_apply]
        exact hgA_mulVec (b.symm w)
      rw [h1]
      have h2 : hA (b.symm w) = b.symm (eA w) := by
        show b.symm ((eA.restrictScalars K) (b (b.symm w))) = b.symm (eA w)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]
      rw [h2, LinearEquiv.apply_symm_apply]
    have heA_mat : LinearMap.toMatrixAlgEquiv' (eA : (Fin m → E) ≃ₗ[E] (Fin m → E)).toLinearMap
        = (A : Matrix (Fin m) (Fin m) E) := by
      show LinearMap.toMatrixAlgEquiv' (ltrd3j2_mulVecEquiv A).toLinearMap
          = (A : Matrix (Fin m) (Fin m) E)
      have h : (ltrd3j2_mulVecEquiv A).toLinearMap
          = Matrix.toLinAlgEquiv' (A : Matrix (Fin m) (Fin m) E) := by
        apply LinearMap.ext
        intro v
        rw [Matrix.toLinAlgEquiv'_apply]
        rfl
      rw [h, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
    apply Units.ext
    show LinearMap.toMatrixAlgEquiv' (eg ⟨gA, hmemA⟩).toLinearMap
        = (A : Matrix (Fin m) (Fin m) E)
    have hlin : (eg ⟨gA, hmemA⟩).toLinearMap =
        (eA : (Fin m → E) ≃ₗ[E] (Fin m → E)).toLinearMap := by
      apply LinearMap.ext
      intro w
      exact hfgA w
    rw [hlin, heA_mat]
  refine ⟨MulEquiv.ofBijective Φhom ⟨hinj, hsurj⟩, ?_⟩
  intro g v
  show b (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v)
      = ((ltrd3j2_matrixUnit (eg g) : (Matrix (Fin m) (Fin m) E)ˣ) : Matrix (Fin m) (Fin m) E)
          *ᵥ (b v)
  rw [ltrd3j2_matrixUnit_mulVec]
  show b (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v)
      = b ((gL g) (b.symm (b v)))
  rw [LinearEquiv.symm_apply_apply]
  simp [gL, gU, ltrd3j2_mulVecEquiv_apply]

end

end S2MathAs3_1624

end

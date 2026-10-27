module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Orthogonality
public import Mathlib.LinearAlgebra.Matrix.Permutation

namespace CFSG
end CFSG
open CFSG

open scoped BigOperators

noncomputable section

namespace CFSG.Theory.Character

open _root_.Representation
open Theory.Representation

open Theory.Character

attribute [local instance] Fintype.ofFinite

variable {L : Type*} [Group L] [Finite L]

@[expose] public def normalSubgroupConjMulEquiv
    (N : Subgroup L) [N.Normal] (g : L) : N ≃* N where
  toFun x :=
    ⟨g * (x : L) * g⁻¹,
      Subgroup.Normal.conj_mem (inferInstance : N.Normal) (x : L) x.2 g⟩
  invFun x :=
    ⟨g⁻¹ * (x : L) * g, by
      simpa using
        ((inferInstance : N.Normal).conj_mem (x : L) x.2 g⁻¹)⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

@[expose] public def conjClassesConjPerm
    (N : Subgroup L) [N.Normal] (g : L) :
    Equiv.Perm (ConjClasses N) where
  toFun := ConjClasses.map (normalSubgroupConjMulEquiv N g).toMonoidHom
  invFun := ConjClasses.map (normalSubgroupConjMulEquiv N g⁻¹).toMonoidHom
  left_inv c := by
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    apply ConjClasses.mk_eq_mk_iff_isConj.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp [normalSubgroupConjMulEquiv, mul_assoc]
  right_inv c := by
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    apply ConjClasses.mk_eq_mk_iff_isConj.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp [normalSubgroupConjMulEquiv, mul_assoc]

omit [Finite L] in
public theorem conjClassesConjPerm_mk
    (N : Subgroup L) [N.Normal] (g : L) (x : N) :
    conjClassesConjPerm N g (ConjClasses.mk x) =
      ConjClasses.mk ((normalSubgroupConjMulEquiv N g) x) := rfl

omit [Finite L] in
public theorem conjClassesConjPerm_symm_mk
    (N : Subgroup L) [N.Normal] (g : L) (x : N) :
    (conjClassesConjPerm N g).symm (ConjClasses.mk x) =
      ConjClasses.mk ((normalSubgroupConjMulEquiv N g).symm x) := by
  change ConjClasses.mk ((normalSubgroupConjMulEquiv N g⁻¹) x) =
    ConjClasses.mk ((normalSubgroupConjMulEquiv N g).symm x)
  congr 1
  apply Subtype.ext
  simp [normalSubgroupConjMulEquiv, mul_assoc]
@[expose] public def classFunctionConjLinearEquiv
    (N : Subgroup L) [N.Normal] (g : L) :
    ConjClassFunction N ≃ₗ[ℂ] ConjClassFunction N where
  toFun φ := fun c => φ ((conjClassesConjPerm N g).symm c)
  invFun φ := fun c => φ ((conjClassesConjPerm N g) c)
  left_inv φ := by ext c; simp
  right_inv φ := by ext c; simp
  map_add' φ ψ := by ext c; simp
  map_smul' a φ := by ext c; simp

public theorem classFunctionConjLinearEquiv_basisFun
    (N : Subgroup L) [N.Normal] (g : L)
    (c : ConjClasses N) :
    classFunctionConjLinearEquiv N g
        ((Pi.basisFun ℂ (ConjClasses N)) c) =
      (Pi.basisFun ℂ (ConjClasses N))
        ((conjClassesConjPerm N g) c) := by
  classical
  ext d
  by_cases hsymm : (conjClassesConjPerm N g).symm d = c
  · have hdc : d = (conjClassesConjPerm N g) c := by
      rw [← hsymm]
      simp
    rw [hdc]
    have hinv :
        (conjClassesConjPerm N g).symm
          ((conjClassesConjPerm N g) c) = c := by
      simp
    change
      ((Pi.basisFun ℂ (ConjClasses N)) c)
          ((conjClassesConjPerm N g).symm
            ((conjClassesConjPerm N g) c)) =
        ((Pi.basisFun ℂ (ConjClasses N))
          ((conjClassesConjPerm N g) c))
            ((conjClassesConjPerm N g) c)
    simp [hinv]
  · have hdc : d ≠ (conjClassesConjPerm N g) c := by
      intro hdc
      apply hsymm
      rw [hdc]
      simp
    simp [classFunctionConjLinearEquiv, hsymm, hdc]
omit [Finite L] in
public theorem classFunctionConjLinearEquiv_characterClassFunction
    (N : Subgroup L) [N.Normal] (g : L)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ N V) :
    classFunctionConjLinearEquiv N g (characterClassFunction rho) =
      characterClassFunction
        (show Representation ℂ N V from
          rho.comp (normalSubgroupConjMulEquiv N g).symm.toMonoidHom) := by
  let sigma : Representation ℂ N V :=
    rho.comp (normalSubgroupConjMulEquiv N g).symm.toMonoidHom
  change classFunctionConjLinearEquiv N g (characterClassFunction rho) =
    characterClassFunction sigma
  ext c
  rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
  change characterClassFunction rho
      ((conjClassesConjPerm N g).symm (ConjClasses.mk x)) =
    characterClassFunction sigma (ConjClasses.mk x)
  rw [conjClassesConjPerm_symm_mk]
  rfl

public theorem classFunctionInner_classFunctionConjLinearEquiv
    (N : Subgroup L) [N.Normal] (g : L)
    (phi psi : ConjClassFunction N) :
    classFunctionInner (classFunctionConjLinearEquiv N g phi)
        (classFunctionConjLinearEquiv N g psi) =
      classFunctionInner phi psi := by
  classical
  let : Fintype N := Fintype.ofFinite N
  unfold classFunctionInner
  congr 1
  have happ (x : N) :
      classFunctionConjLinearEquiv N g phi (ConjClasses.mk x) =
        phi (ConjClasses.mk ((normalSubgroupConjMulEquiv N g).symm x)) := by
    change phi ((conjClassesConjPerm N g).symm (ConjClasses.mk x)) =
      phi (ConjClasses.mk ((normalSubgroupConjMulEquiv N g).symm x))
    rw [conjClassesConjPerm_symm_mk]
  have happ' (x : N) :
      classFunctionConjLinearEquiv N g psi (ConjClasses.mk x) =
        psi (ConjClasses.mk ((normalSubgroupConjMulEquiv N g).symm x)) := by
    change psi ((conjClassesConjPerm N g).symm (ConjClasses.mk x)) =
      psi (ConjClasses.mk ((normalSubgroupConjMulEquiv N g).symm x))
    rw [conjClassesConjPerm_symm_mk]
  simp_rw [happ, happ']
  simpa using (normalSubgroupConjMulEquiv N g).symm.sum_comp
    (fun x : N => phi (ConjClasses.mk x) * star (psi (ConjClasses.mk x)))
public theorem classFunctionConjLinearEquiv_isIrreducibleCharacter
    (N : Subgroup L) [N.Normal] (g : L)
    {chi : ConjClassFunction N}
    (hchi : IsIrreducibleConjCharacter chi) :
    IsIrreducibleConjCharacter (classFunctionConjLinearEquiv N g chi) := by
  rcases hchi.1 with ⟨n, rho, hrho⟩
  constructor
  · refine ⟨n, rho.comp (normalSubgroupConjMulEquiv N g).symm.toMonoidHom, ?_⟩
    rw [← classFunctionConjLinearEquiv_characterClassFunction N g rho, ← hrho]
  · rw [classFunctionInner_classFunctionConjLinearEquiv]
    exact hchi.2

public theorem trace_linearEquiv_eq_ncard_fixedPoints_of_permutes_basis
    {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module ℂ M]
    (b : Module.Basis ι ℂ M)
    (sigma : Equiv.Perm ι)
    (T : M ≃ₗ[ℂ] M)
    (hT : ∀ i, T (b i) = b (sigma i)) :
    LinearMap.trace ℂ M T.toLinearMap =
      ((Function.fixedPoints sigma).ncard : ℂ) := by
  classical
  have hmatrix :
      LinearMap.toMatrix b b T.toLinearMap = (sigma⁻¹).permMatrix ℂ := by
    ext i j
    by_cases h : sigma j = i
    · have hsymm : sigma⁻¹ i = j := by
        rw [← h]
        simp
      simp [LinearMap.toMatrix_apply, hT, h, hsymm]
    · have hsymm : sigma⁻¹ i ≠ j := by
        intro hsymm
        apply h
        rw [← hsymm]
        simp
      have hsymm' : (_root_.Equiv.symm sigma) i ≠ j := by
        simpa using hsymm
      rw [LinearMap.toMatrix_apply]
      have hentry :
          (b.repr ((T : M →ₗ[ℂ] M) (b j))) i =
            (b.repr (b (sigma j))) i := by
        simpa using congrArg (fun v => (b.repr v) i) (hT j)
      rw [hentry]
      simp [h, hsymm']
  calc
    LinearMap.trace ℂ M T.toLinearMap =
        Matrix.trace (LinearMap.toMatrix b b T.toLinearMap) := by
          rw [LinearMap.trace_eq_matrix_trace ℂ b T.toLinearMap]
    _ = Matrix.trace ((sigma⁻¹).permMatrix ℂ) := by rw [hmatrix]
    _ = ((Function.fixedPoints (sigma⁻¹ : Equiv.Perm ι)).ncard : ℂ) := by
          exact Matrix.trace_permutation (R := ℂ) (σ := sigma⁻¹)
    _ = ((Function.fixedPoints sigma).ncard : ℂ) := by
      congr 1
      congr 1
      ext i
      constructor
      · intro hi
        change sigma⁻¹ i = i at hi
        calc
          sigma i = sigma (sigma⁻¹ i) := by rw [hi]
          _ = i := by simp
      · intro hi
        change sigma i = i at hi
        apply sigma.injective
        simp [hi]

omit [Finite L] in
public theorem classFunctionConjLinearEquiv_symm_apply
    (N : Subgroup L) [N.Normal] (g : L)
    (chi : ConjClassFunction N) :
    (classFunctionConjLinearEquiv N g).symm chi =
      classFunctionConjLinearEquiv N g⁻¹ chi := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
  change chi (conjClassesConjPerm N g (ConjClasses.mk x)) =
    chi ((conjClassesConjPerm N g⁻¹).symm (ConjClasses.mk x))
  rw [conjClassesConjPerm_mk, conjClassesConjPerm_symm_mk]
  have h :
      (normalSubgroupConjMulEquiv N g) x =
        (normalSubgroupConjMulEquiv N g⁻¹).symm x := by
    apply Subtype.ext
    simp [normalSubgroupConjMulEquiv, mul_assoc]
  exact congrArg chi (congrArg ConjClasses.mk h)

@[expose] public def irreducibleConjClassFunctionPerm
    (N : Subgroup L) [N.Normal] (g : L) :
    Equiv.Perm {chi : ConjClassFunction N // IsIrreducibleConjCharacter chi} where
  toFun chi :=
    ⟨classFunctionConjLinearEquiv N g chi.1,
      classFunctionConjLinearEquiv_isIrreducibleCharacter N g chi.2⟩
  invFun chi :=
    ⟨classFunctionConjLinearEquiv N g⁻¹ chi.1,
      classFunctionConjLinearEquiv_isIrreducibleCharacter N g⁻¹ chi.2⟩
  left_inv chi := by
    apply Subtype.ext
    change classFunctionConjLinearEquiv N g⁻¹
        (classFunctionConjLinearEquiv N g chi.1) = chi.1
    rw [← classFunctionConjLinearEquiv_symm_apply N g]
    simp
  right_inv chi := by
    apply Subtype.ext
    change classFunctionConjLinearEquiv N g
        (classFunctionConjLinearEquiv N g⁻¹ chi.1) = chi.1
    rw [← classFunctionConjLinearEquiv_symm_apply N g]
    simp

public theorem trace_classFunctionConjLinearEquiv_eq_fixed_irreducibles
    (N : Subgroup L) [N.Normal] (g : L) :
    LinearMap.trace ℂ (ConjClassFunction N)
        (classFunctionConjLinearEquiv N g).toLinearMap =
      ((Function.fixedPoints
          (irreducibleConjClassFunctionPerm N g)).ncard : ℂ) := by
  classical
  rcases irreducible_characters_form_basis (G := N) with
    ⟨ι, hι, chi, hchi, b, hb⟩
  let : Fintype ι := hι
  let f :
      ι → {chi : ConjClassFunction N // IsIrreducibleConjCharacter chi} :=
    fun i => ⟨chi i, hchi.1 i⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · intro i j hij
      apply hchi.2.2
      exact congrArg Subtype.val hij
    · intro psi
      rcases hchi.2.1 psi.1 psi.2 with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
  let e : ι ≃ {chi : ConjClassFunction N // IsIrreducibleConjCharacter chi} :=
    Equiv.ofBijective f hf_bij
  let : Fintype {chi : ConjClassFunction N // IsIrreducibleConjCharacter chi} :=
    Fintype.ofEquiv ι e
  let bIrr :
      Module.Basis
        {chi : ConjClassFunction N // IsIrreducibleConjCharacter chi}
        ℂ (ConjClassFunction N) :=
    b.reindex e
  have hbIrr :
      ∀ psi : {chi : ConjClassFunction N // IsIrreducibleConjCharacter chi},
        bIrr psi = psi.1 := by
    intro psi
    dsimp [bIrr]
    rw [Module.Basis.reindex_apply, hb]
    have h := congrArg Subtype.val (_root_.Equiv.apply_symm_apply e psi)
    dsimp [e, f] at h
    exact h
  exact
    trace_linearEquiv_eq_ncard_fixedPoints_of_permutes_basis
      bIrr (irreducibleConjClassFunctionPerm N g)
      (classFunctionConjLinearEquiv N g)
      (by
        intro psi
        rw [hbIrr, hbIrr]
        rfl)

public theorem trace_classFunctionConjLinearEquiv_eq_fixed_conjClasses
    (N : Subgroup L) [N.Normal] (g : L) :
    LinearMap.trace ℂ (ConjClassFunction N)
        (classFunctionConjLinearEquiv N g).toLinearMap =
      ((Function.fixedPoints (conjClassesConjPerm N g)).ncard : ℂ) := by
  classical
  exact
    trace_linearEquiv_eq_ncard_fixedPoints_of_permutes_basis
      (Pi.basisFun ℂ (ConjClasses N)) (conjClassesConjPerm N g)
      (classFunctionConjLinearEquiv N g)
      (classFunctionConjLinearEquiv_basisFun N g)

public theorem fixed_irreducible_ncard_eq_fixed_conjClasses
    (N : Subgroup L) [N.Normal] (g : L) :
    (Function.fixedPoints
        (irreducibleConjClassFunctionPerm N g)).ncard =
      (Function.fixedPoints (conjClassesConjPerm N g)).ncard := by
  have hIrr :=
    trace_classFunctionConjLinearEquiv_eq_fixed_irreducibles N g
  have hClass :=
    trace_classFunctionConjLinearEquiv_eq_fixed_conjClasses N g
  exact_mod_cast hIrr.symm.trans hClass
public theorem exists_nontrivial_fixed_conjClass_of_two_fixed_irreducible
    (N : Subgroup L) [N.Normal] (g : L)
    {chi psi : ConjClassFunction N}
    (hchiIrr : IsIrreducibleConjCharacter chi)
    (hpsiIrr : IsIrreducibleConjCharacter psi)
    (hchiFix : classFunctionConjLinearEquiv N g chi = chi)
    (hpsiFix : classFunctionConjLinearEquiv N g psi = psi)
    (hne : chi ≠ psi) :
    ∃ x : N, x ≠ 1 ∧
      IsConj ((normalSubgroupConjMulEquiv N g) x) x := by
  classical
  rcases irreducible_characters_form_basis (G := N) with
    ⟨ι, hι, theta, htheta, _basis, _hbasis⟩
  let : Fintype ι := hι
  let f : ι → {eta : ConjClassFunction N // IsIrreducibleConjCharacter eta} :=
    fun i => ⟨theta i, htheta.1 i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply htheta.2.2
      exact congrArg Subtype.val hij
    · intro eta
      rcases htheta.2.1 eta.1 eta.2 with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
  let e : ι ≃ {eta : ConjClassFunction N // IsIrreducibleConjCharacter eta} :=
    _root_.Equiv.ofBijective f hf
  let : Fintype {eta : ConjClassFunction N // IsIrreducibleConjCharacter eta} :=
    Fintype.ofEquiv ι e
  let a : {eta : ConjClassFunction N // IsIrreducibleConjCharacter eta} :=
    ⟨chi, hchiIrr⟩
  let b : {eta : ConjClassFunction N // IsIrreducibleConjCharacter eta} :=
    ⟨psi, hpsiIrr⟩
  have ha :
      a ∈ Function.fixedPoints (irreducibleConjClassFunctionPerm N g) := by
    rw [Function.mem_fixedPoints_iff]
    apply Subtype.ext
    exact hchiFix
  have hb :
      b ∈ Function.fixedPoints (irreducibleConjClassFunctionPerm N g) := by
    rw [Function.mem_fixedPoints_iff]
    apply Subtype.ext
    exact hpsiFix
  have hab : a ≠ b := by
    intro hab
    exact hne (congrArg Subtype.val hab)
  have hIrrLarge :
      1 < (Function.fixedPoints
        (irreducibleConjClassFunctionPerm N g)).ncard := by
    rw [Set.one_lt_ncard]
    exact ⟨a, ha, b, hb, hab⟩
  have hClassLarge :
      1 < (Function.fixedPoints (conjClassesConjPerm N g)).ncard := by
    rw [← fixed_irreducible_ncard_eq_fixed_conjClasses N g]
    exact hIrrLarge
  rcases Set.exists_ne_of_one_lt_ncard hClassLarge
      (ConjClasses.mk (1 : N)) with ⟨c, hc, hcne⟩
  rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
  have hxne : x ≠ 1 := by
    intro hx
    apply hcne
    rw [hx]
  refine ⟨x, hxne, ?_⟩
  rw [Function.mem_fixedPoints_iff, conjClassesConjPerm_mk] at hc
  exact ConjClasses.mk_eq_mk_iff_isConj.mp hc
end CFSG.Theory.Character

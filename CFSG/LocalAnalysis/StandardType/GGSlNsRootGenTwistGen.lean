module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTwist
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB Multiplicative

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {g : K[X]} [Fact (Irreducible g)]
  {n s r p : ℕ} [Fact p.Prime]

omit [Fintype K] [CharP K 2] in
private theorem rootPB_gen : (rootPB g).gen = AdjoinRoot.root g := by
  rw [rootPB]
  exact AdjoinRoot.powerBasis_gen _

private noncomputable def crossShift (i j : Fin s) (f : AdjoinRoot g →ₗ[K] AdjoinRoot g) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K]
      ((Fin s → AdjoinRoot g) × (Fin r → K)) where
  toFun x := (Pi.single i (f (x.1 j)), 0)
  map_add' x y := by
    refine Prod.ext (funext fun m => ?_) (by simp)
    simp [Pi.single_add, map_add]
  map_smul' c x := by
    refine Prod.ext (funext fun m => ?_) (by simp)
    simp [Pi.single_smul, map_smul]

private noncomputable def crossMap (i j : Fin s) (f : AdjoinRoot g →ₗ[K] AdjoinRoot g) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K]
      ((Fin s → AdjoinRoot g) × (Fin r → K)) :=
  LinearMap.id + crossShift i j f

omit [Fintype K] [CharP K 2] in
private theorem crossMap_apply (i j : Fin s) (f : AdjoinRoot g →ₗ[K] AdjoinRoot g)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    crossMap i j f x = (x.1 + Pi.single i (f (x.1 j)), x.2) := by
  refine Prod.ext ?_ ?_
  · simp [crossMap, crossShift]
  · simp [crossMap, crossShift]

omit [Fintype K] [CharP K 2] in
private theorem crossMap_comp {i j : Fin s} (hij : i ≠ j)
    (u v : AdjoinRoot g →ₗ[K] AdjoinRoot g) :
    (crossMap (r := r) i j u) ∘ₗ (crossMap (r := r) i j v) =
      crossMap (r := r) i j (u + v) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  simp only [crossMap_apply]
  refine Prod.ext (funext fun m => ?_) rfl
  by_cases hm : m = i
  · subst hm
    have hji : j ≠ m := Ne.symm hij
    simp only [Prod.mk_add_mk, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hji,
      map_add, map_zero, LinearMap.add_apply]
    rw [add_zero, add_assoc, add_comm (v (x.1 j)) (u (x.1 j))]
  · simp only [Prod.mk_add_mk, Pi.add_apply, Pi.single_eq_of_ne hm, add_zero, zero_add]

private noncomputable def crossMat (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i j : Fin s) (f : AdjoinRoot g →ₗ[K] AdjoinRoot g) : Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrix' ((frameCoords g ε).toLinearMap ∘ₗ crossMap i j f ∘ₗ
    (frameCoords g ε).symm.toLinearMap)

omit [Fintype K] [CharP K 2] in
private theorem frameForm_crossMat (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i j : Fin s) (f : AdjoinRoot g →ₗ[K] AdjoinRoot g) :
    frameForm g ε (crossMat ε i j f) = crossMap i j f := by
  refine LinearMap.ext fun x => ?_
  rw [frameForm_apply, crossMat, LinearMap.toMatrix'_mulVec]
  simp

omit [Fintype K] [CharP K 2] in
private theorem crossMat_comp (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) (u v : AdjoinRoot g →ₗ[K] AdjoinRoot g) :
    crossMat (r := r) ε i j (u + v) =
      crossMat (r := r) ε i j u * crossMat (r := r) ε i j v := by
  apply frameForm_injective g ε
  rw [frameForm_mul, frameForm_crossMat, frameForm_crossMat, frameForm_crossMat]
  exact (crossMap_comp hij u v).symm

omit [Fintype K] [CharP K 2] in
private theorem crossMap_mul_apply {i j : Fin s} (hij : i ≠ j) (α : AdjoinRoot g)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    crossMap i j (LinearMap.mulLeft K α) x =
      (Matrix.transvection i j α *ᵥ x.1, x.2) := by
  rw [crossMap_apply]
  refine Prod.ext (funext fun m => ?_) rfl
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  by_cases hm : m = i
  · subst hm
    simp [Pi.single_eq_same, LinearMap.mulLeft_apply, smul_eq_mul]
  · simp [Pi.single_eq_of_ne hm]

omit [Fintype K] [CharP K 2] in
private theorem crossMat_mul (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) (α : AdjoinRoot g) :
    crossMat ε i j (LinearMap.mulLeft K α) =
      thetaMat g ε (Matrix.transvection i j α) := by
  apply frameForm_injective g ε
  rw [frameForm_crossMat, frameForm_thetaMat]
  refine LinearMap.ext fun x => ?_
  rw [blockAct_apply, crossMap_mul_apply hij α x]

omit [CharP K 2] in
private theorem crossMap_conj_source_apply (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) {i j : Fin s} (hij : i ≠ j) (α : AdjoinRoot g)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    (negMove g j) (blockAct g (Matrix.transvection i j α) ((negMove g j) x)) =
      crossMap i j
        ((LinearMap.mulLeft K α) ∘ₗ (frobAlgEquiv g).toLinearMap) x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp only [negMove_apply, blockAct_apply]
  refine Prod.ext (funext fun m => ?_) (by simp [crossMap_apply])
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  by_cases hm : m = i
  · subst hm
    have hji : j ≠ m := Ne.symm hij
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hji,
      smul_eq_mul, mul_one, negTau_apply_of_ne g hij, negTau_apply_self, crossMap_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, Equiv.refl_apply]
    rfl
  · simp only [Pi.single_eq_of_ne hm, Pi.smul_apply, smul_zero, add_zero, Pi.add_apply,
      negTau_apply_apply g hζ hpK, crossMap_apply]

omit [CharP K 2] in
private theorem crossMap_conj_target_apply (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) {i j : Fin s} (hij : i ≠ j) (α : AdjoinRoot g)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    (negMove g j) (blockAct g (Matrix.transvection j i α) ((negMove g j) x)) =
      crossMap (i := j) (j := i)
        ((LinearMap.mulLeft K (frobAlgEquiv g α)) ∘ₗ (frobAlgEquiv g).toLinearMap) x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp only [negMove_apply, blockAct_apply]
  refine Prod.ext (funext fun m => ?_) (by simp [crossMap_apply])
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  by_cases hm : m = j
  · subst hm
    have hji : i ≠ m := hij
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hji,
      smul_eq_mul, mul_one, negTau_apply_of_ne g hij, negTau_apply_self, map_add, map_mul,
      frobAlgEquiv_apply_apply g hζ hpK, crossMap_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, Equiv.refl_apply]
    rfl
  · simp only [Pi.single_eq_of_ne hm, Pi.smul_apply, smul_zero, add_zero, Pi.add_apply,
      negTau_apply_apply g hζ hpK, crossMap_apply]

omit [CharP K 2] in
private theorem frameForm_conj_source (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) (α : AdjoinRoot g) :
    frameForm g ε (negMat g ε j * thetaMat g ε (Matrix.transvection i j α) * negMat g ε j) =
      crossMap i j
        ((LinearMap.mulLeft K α) ∘ₗ (frobAlgEquiv g).toLinearMap) := by
  rw [frameForm_mul, frameForm_mul, frameForm_negMat, frameForm_thetaMat]
  refine LinearMap.ext fun x => ?_
  change (negMove g j) (blockAct g (Matrix.transvection i j α) ((negMove g j) x)) =
    crossMap i j ((LinearMap.mulLeft K α) ∘ₗ (frobAlgEquiv g).toLinearMap) x
  exact crossMap_conj_source_apply hζ hpK hij α x

omit [CharP K 2] in
private theorem frameForm_conj_target (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) (α : AdjoinRoot g) :
    frameForm g ε (negMat g ε j * thetaMat g ε (Matrix.transvection j i α) * negMat g ε j) =
      crossMap (i := j) (j := i)
        ((LinearMap.mulLeft K (frobAlgEquiv g α)) ∘ₗ (frobAlgEquiv g).toLinearMap) := by
  rw [frameForm_mul, frameForm_mul, frameForm_negMat, frameForm_thetaMat]
  refine LinearMap.ext fun x => ?_
  change (negMove g j) (blockAct g (Matrix.transvection j i α) ((negMove g j) x)) =
    crossMap (i := j) (j := i)
      ((LinearMap.mulLeft K (frobAlgEquiv g α)) ∘ₗ (frobAlgEquiv g).toLinearMap) x
  exact crossMap_conj_target_apply hζ hpK hij α x

omit [CharP K 2] in
private theorem crossMat_conj_source (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) (α : AdjoinRoot g) :
    negMat g ε j * thetaMat g ε (Matrix.transvection i j α) * negMat g ε j =
      crossMat ε i j
        ((LinearMap.mulLeft K α) ∘ₗ (frobAlgEquiv g).toLinearMap) := by
  apply frameForm_injective g ε
  rw [frameForm_conj_source hζ hpK ε hij α, frameForm_crossMat]

omit [CharP K 2] in
private theorem crossMat_conj_target (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) (α : AdjoinRoot g) :
    negMat g ε j * thetaMat g ε (Matrix.transvection j i α) * negMat g ε j =
      crossMat (i := j) (j := i) ε
        ((LinearMap.mulLeft K (frobAlgEquiv g α)) ∘ₗ (frobAlgEquiv g).toLinearMap) := by
  apply frameForm_injective g ε
  rw [frameForm_conj_target hζ hpK ε hij α, frameForm_crossMat]

private theorem exists_mul_add_frob (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1)
    (f : AdjoinRoot g →ₗ[K] AdjoinRoot g) :
    ∃ α β : AdjoinRoot g,
      f = LinearMap.mulLeft K α +
        (LinearMap.mulLeft K β) ∘ₗ (frobAlgEquiv g).toLinearMap := by
  have hp : p.Prime := Fact.out
  have hpK0 : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hdim : (rootPB g).dim = 2 := SpNS.rootPB_dim_eq_two hp hp2 hpK0 hgd hpK
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) p :=
    NSFrame.root_isPrimitiveRoot hp hpK0 hgd
  have hζ0 : AdjoinRoot.root g ≠ 0 := hprim.ne_zero hp.ne_zero
  have hζne : AdjoinRoot.root g ≠ (AdjoinRoot.root g)⁻¹ := by
    intro h
    have h2 : AdjoinRoot.root g ^ 2 = 1 := by
      have h3 : AdjoinRoot.root g * AdjoinRoot.root g = 1 := by
        nth_rewrite 2 [h]
        exact mul_inv_cancel₀ hζ0
      simpa [pow_two] using h3
    have hdvd : p ∣ 2 := (hprim.pow_eq_one_iff_dvd 2).mp h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  set ζ := AdjoinRoot.root g with hζdef
  set β : AdjoinRoot g := (f ζ - ζ * f 1) / (ζ⁻¹ - ζ) with hβ
  refine ⟨f 1 - β, β, ?_⟩
  have hβeq : β * (ζ⁻¹ - ζ) = f ζ - ζ * f 1 := by
    rw [hβ, div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hζne))]
  refine (rootPB g).basis.ext fun b => ?_
  have hb : b.val = 0 ∨ b.val = 1 := by
    have := b.isLt
    omega
  rw [PowerBasis.basis_eq_pow]
  rcases hb with h | h
  · rw [h, pow_zero]
    simp [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, map_one,
      sub_add_cancel]
  · rw [h, pow_one, rootPB_gen]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      AlgEquiv.toLinearMap_apply, frobAlgEquiv_root g hζ hpK]
    calc f ζ = ζ * f 1 + (f ζ - ζ * f 1) := by ring
      _ = ζ * f 1 + β * (ζ⁻¹ - ζ) := by rw [← hβeq]
      _ = (f 1 - β) * ζ + β * ζ⁻¹ := by ring

omit [Fintype K] [CharP K 2] in
private theorem theta_transvection_mem_pairBlock
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (α : AdjoinRoot g) :
    theta g ε (SpecialLinearGroup.transvection hij α) ∈ pairBlock g ε i j := by
  rw [pairBlock, Subgroup.mem_map]
  exact ⟨_, SLRep.transvection_mem_coordBlockSL (by simp) (by simp) hij α, rfl⟩

omit [Fintype K] [CharP K 2] in
private theorem theta_transvection_mem_pairBlock_swap
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (α : AdjoinRoot g) :
    theta g ε (SpecialLinearGroup.transvection hij.symm α) ∈ pairBlock g ε i j := by
  rw [pairBlock, Subgroup.mem_map]
  exact ⟨_, SLRep.transvection_mem_coordBlockSL (by simp) (by simp) hij.symm α, rfl⟩

private noncomputable def coordMap (a b : Fin (rootPB g).dim) (t : K) :
    AdjoinRoot g →ₗ[K] AdjoinRoot g where
  toFun y := (t * (rootPB g).basis.repr y b) • (rootPB g).basis a
  map_add' y z := by
    simp only [map_add, Finsupp.add_apply, mul_add, add_smul]
  map_smul' c y := by
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, smul_smul, RingHom.id_apply]
    rw [mul_left_comm]

omit [Fintype K] [CharP K 2] in
private theorem coord_eq (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) (a : Fin (rootPB g).dim) :
    coord ε i a = ε.symm (Sum.inl (a, i)) := by
  have h1 : frameCoords g ε ((Pi.single i ((rootPB g).basis a) : Fin s → AdjoinRoot g),
      (0 : Fin r → K)) = Pi.single (coord ε i a) 1 := by
    rw [← frameCoords_symm_single_coord (ε := ε) a i, LinearEquiv.apply_symm_apply]
  have h2 : frameCoords g ε ((Pi.single i ((rootPB g).basis a) : Fin s → AdjoinRoot g),
      (0 : Fin r → K)) = Pi.single (ε.symm (Sum.inl (a, i))) 1 :=
    frameCoords_single_basis ε a i
  have h3 := congrFun (h1.symm.trans h2) (coord ε i a)
  rw [Pi.single_eq_same] at h3
  by_contra hne
  rw [Pi.single_eq_of_ne hne] at h3
  exact one_ne_zero h3

omit [Fintype K] [CharP K 2] in
private theorem frameCoords_coord (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) (i : Fin s)
    (a : Fin (rootPB g).dim) :
    frameCoords g ε x (coord ε i a) = (rootPB g).basis.repr (x.1 i) a := by
  rw [coord_eq, frameCoords_apply, Equiv.apply_symm_apply]
  simp

omit [Fintype K] [CharP K 2] in
private theorem crossMat_coordMap (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (a b : Fin (rootPB g).dim) (t : K) :
    crossMat ε i j (coordMap a b t) =
      Matrix.transvection (coord ε i a) (coord ε j b) t := by
  apply frameForm_injective g ε
  rw [frameForm_crossMat]
  refine LinearMap.ext fun x => ?_
  rw [frameForm_apply]
  apply (frameCoords g ε).injective
  rw [LinearEquiv.apply_symm_apply]
  have hshift : frameCoords g ε (crossShift i j (coordMap a b t) x) =
      (t * (rootPB g).basis.repr (x.1 j) b) • Pi.single (coord ε i a) 1 := by
    have h1 : crossShift i j (coordMap a b t) x =
        (t * (rootPB g).basis.repr (x.1 j) b) •
          ((Pi.single i ((rootPB g).basis a) : Fin s → AdjoinRoot g), (0 : Fin r → K)) := by
      refine Prod.ext ?_ ?_
      · simp [crossShift, coordMap, Pi.single_smul]
      · simp [crossShift]
    rw [h1, map_smul, frameCoords_single_basis, coord_eq]
  rw [crossMap, LinearMap.add_apply, LinearMap.id_apply, map_add, hshift]
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  rw [frameCoords_coord]

private theorem exists_mem_crossMat_direction1 (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hP : pairBlock g ε i j ≤ H) (hT : twistPairBlock g hζ hpK ε i j ≤ H)
    (f : AdjoinRoot g →ₗ[K] AdjoinRoot g) :
    ∃ M ∈ H, (M : Matrix (Fin n) (Fin n) K) = crossMat ε i j f := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨α, β, hf⟩ := exists_mul_add_frob hp2 hpK hgd hζ f
  let N : SpecialLinearGroup (Fin n) K := negSL g hζ hpK ε j
  have hNinv : N⁻¹ = N := inv_eq_of_mul_eq_one_right (negSL_mul_self g hζ hpK ε j)
  let M₁ : SpecialLinearGroup (Fin n) K :=
    theta g ε (SpecialLinearGroup.transvection hij α)
  let M₂ : SpecialLinearGroup (Fin n) K :=
    N * theta g ε (SpecialLinearGroup.transvection hij β) * N
  refine ⟨M₁ * M₂, ?_, ?_⟩
  · refine H.mul_mem ?_ ?_
    · exact hP (theta_transvection_mem_pairBlock ε hij α)
    · refine hT ?_
      rw [twistPairBlock, Subgroup.mem_map]
      refine ⟨theta g ε (SpecialLinearGroup.transvection hij β),
        theta_transvection_mem_pairBlock ε hij β, ?_⟩
      simp [M₂, N, MulAut.conj_apply, hNinv]
  · rw [Matrix.SpecialLinearGroup.coe_mul]
    have hM₁ : ((M₁ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        crossMat ε i j (LinearMap.mulLeft K α) := by
      dsimp [M₁]
      rw [coe_theta]
      exact (crossMat_mul ε hij α).symm
    have hM₂ : ((M₂ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        crossMat ε i j
          ((LinearMap.mulLeft K β) ∘ₗ (frobAlgEquiv g).toLinearMap) := by
      dsimp [M₂]
      have hNmat : ((N : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          negMat g ε j := rfl
      rw [hNmat, coe_theta]
      change negMat g ε j * thetaMat g ε (Matrix.transvection i j β) * negMat g ε j =
        crossMat ε i j
          ((LinearMap.mulLeft K β) ∘ₗ (frobAlgEquiv g).toLinearMap)
      exact crossMat_conj_source hζ hpK ε hij β
    rw [hM₁, hM₂, ← crossMat_comp ε hij, ← hf]

private theorem exists_mem_crossMat_direction2 (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hP : pairBlock g ε i j ≤ H) (hT : twistPairBlock g hζ hpK ε i j ≤ H)
    (f : AdjoinRoot g →ₗ[K] AdjoinRoot g) :
    ∃ M ∈ H, (M : Matrix (Fin n) (Fin n) K) =
      crossMat (i := j) (j := i) ε f := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨α, β, hf⟩ := exists_mul_add_frob hp2 hpK hgd hζ f
  let N : SpecialLinearGroup (Fin n) K := negSL g hζ hpK ε j
  have hNinv : N⁻¹ = N := inv_eq_of_mul_eq_one_right (negSL_mul_self g hζ hpK ε j)
  let M₁ : SpecialLinearGroup (Fin n) K :=
    theta g ε (SpecialLinearGroup.transvection hij.symm α)
  let M₂ : SpecialLinearGroup (Fin n) K :=
    N * theta g ε (SpecialLinearGroup.transvection hij.symm (frobAlgEquiv g β)) * N
  refine ⟨M₁ * M₂, ?_, ?_⟩
  · refine H.mul_mem ?_ ?_
    · exact hP (theta_transvection_mem_pairBlock_swap ε hij α)
    · refine hT ?_
      rw [twistPairBlock, Subgroup.mem_map]
      refine ⟨theta g ε (SpecialLinearGroup.transvection hij.symm (frobAlgEquiv g β)),
        theta_transvection_mem_pairBlock_swap ε hij (frobAlgEquiv g β), ?_⟩
      simp [M₂, N, MulAut.conj_apply, hNinv]
  · rw [Matrix.SpecialLinearGroup.coe_mul]
    have hM₁ : ((M₁ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        crossMat (i := j) (j := i) ε (LinearMap.mulLeft K α) := by
      dsimp [M₁]
      rw [coe_theta]
      exact (crossMat_mul ε hij.symm α).symm
    have hM₂ : ((M₂ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        crossMat (i := j) (j := i) ε
          ((LinearMap.mulLeft K β) ∘ₗ (frobAlgEquiv g).toLinearMap) := by
      dsimp [M₂]
      have hNmat : ((N : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          negMat g ε j := rfl
      rw [hNmat, coe_theta]
      change negMat g ε j * thetaMat g ε
          (Matrix.transvection j i (frobAlgEquiv g β)) * negMat g ε j =
        crossMat (i := j) (j := i) ε
          ((LinearMap.mulLeft K β) ∘ₗ (frobAlgEquiv g).toLinearMap)
      rw [crossMat_conj_target hζ hpK ε hij (frobAlgEquiv g β)]
      rw [frobAlgEquiv_apply_apply g hζ hpK β]
    rw [hM₁, hM₂, ← crossMat_comp ε hij.symm, ← hf]

theorem transvection_mem_of_pairBlock_twistPairBlock (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    {H : Subgroup (SpecialLinearGroup (Fin n) K)} (hP : pairBlock g ε i j ≤ H)
    (hT : twistPairBlock g hζ hpK ε i j ≤ H) (a b : Fin (rootPB g).dim) (t : K) :
    SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij a b) t ∈ H ∧
      SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij.symm b a) t ∈ H := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  constructor
  · obtain ⟨M, hM, hMmat⟩ := exists_mem_crossMat_direction1 hp2 hpK hgd hζ ε hij hP hT
      (coordMap a b t)
    have hTM : SpecialLinearGroup.transvection
        (i := coord ε i a) (j := coord ε j b)
        (coord_inl_ne_coord_inl (ε := ε) hij a b) t = M := by
      apply Subtype.ext
      rw [show ((SpecialLinearGroup.transvection
          (i := coord ε i a) (j := coord ε j b)
          (coord_inl_ne_coord_inl (ε := ε) hij a b) t :
            SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          Matrix.transvection (coord ε i a) (coord ε j b) t from rfl,
        hMmat, crossMat_coordMap (ε := ε) (i := i) (j := j)
          (a := a) (b := b) t]
    rw [hTM]
    exact hM
  · obtain ⟨M, hM, hMmat⟩ := exists_mem_crossMat_direction2 hp2 hpK hgd hζ ε hij hP hT
      (coordMap b a t)
    have hTM : SpecialLinearGroup.transvection
        (i := coord ε j b) (j := coord ε i a)
        (coord_inl_ne_coord_inl (ε := ε) hij.symm b a) t = M := by
      apply Subtype.ext
      rw [show ((SpecialLinearGroup.transvection
          (i := coord ε j b) (j := coord ε i a)
          (coord_inl_ne_coord_inl (ε := ε) hij.symm b a) t :
            SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          Matrix.transvection (coord ε j b) (coord ε i a) t from rfl,
        hMmat, crossMat_coordMap (ε := ε) (i := j) (j := i)
          (a := b) (b := a) t]
    rw [hTM]
    exact hM

theorem iSup_pairBlock_twistPairBlock_avoid_eq_top (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin 0) (hs : 3 ≤ s) (i₀ j₀ : Fin s) :
    (⨆ (i : Fin s) (j : Fin s) (_ : i ≠ j ∧ ({i, j} : Finset (Fin s)) ≠ {i₀, j₀}),
      pairBlock g ε i j ⊔ twistPairBlock g hζ hpK ε i j) = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  have hpK0 : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hdim : (rootPB g).dim = 2 := SpNS.rootPB_dim_eq_two hp hp2 hpK0 hgd hpK
  let H : Subgroup (SpecialLinearGroup (Fin n) K) :=
    ⨆ (i : Fin s) (j : Fin s) (_ : i ≠ j ∧ ({i, j} : Finset (Fin s)) ≠ {i₀, j₀}),
      pairBlock g ε i j ⊔ twistPairBlock g hζ hpK ε i j
  change H = ⊤
  have hpair : ∀ (i j : Fin s), i ≠ j → ({i, j} : Finset (Fin s)) ≠ {i₀, j₀} →
      pairBlock g ε i j ≤ H := by
    intro i j hij hne x hx
    exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem j
      (Subgroup.mem_iSup_of_mem ⟨hij, hne⟩ (Subgroup.mem_sup_left hx)))
  have htwist : ∀ (i j : Fin s), i ≠ j → ({i, j} : Finset (Fin s)) ≠ {i₀, j₀} →
      twistPairBlock g hζ hpK ε i j ≤ H := by
    intro i j hij hne x hx
    exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem j
      (Subgroup.mem_iSup_of_mem ⟨hij, hne⟩ (Subgroup.mem_sup_right hx)))
  have hcross : ∀ (i j : Fin s) (hij : i ≠ j),
      ({i, j} : Finset (Fin s)) ≠ {i₀, j₀} → ∀ (a b : Fin (rootPB g).dim) (t : K),
      SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij a b) t ∈ H := by
    intro i j hij hne a b t
    exact (transvection_mem_of_pairBlock_twistPairBlock hp2 hpK hgd hζ ε hij
      (hpair i j hij hne) (htwist i j hij hne) a b t).1
  have hcoord : ∀ x : Fin n, ∃ (a : Fin (rootPB g).dim) (i : Fin s), x = coord ε i a := by
    intro x
    rcases hx : ε x with ⟨a, i⟩ | z
    · exact ⟨a, i, by rw [coord_eq, ← hx, Equiv.symm_apply_apply]⟩
    · exact absurd z.isLt (by omega)
  have hex : ∀ i : Fin s, ∃ k : Fin s, k ≠ i ∧ ({i, k} : Finset (Fin s)) ≠ {i₀, j₀} := by
    intro i
    by_contra h
    have h' : ∀ k : Fin s, k ≠ i → ({i, k} : Finset (Fin s)) = {i₀, j₀} := by
      intro k hk
      by_contra hk'
      exact h ⟨k, hk, hk'⟩
    have hcard : 2 ≤ (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨k1, hk1, k2, hk2, hk12⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.erase i).card)
    have hk1' : k1 ≠ i := (Finset.mem_erase.mp hk1).1
    have hk2' : k2 ≠ i := (Finset.mem_erase.mp hk2).1
    have heq : ({i, k1} : Finset (Fin s)) = {i, k2} := by rw [h' k1 hk1', h' k2 hk2']
    have hmem : k1 ∈ ({i, k2} : Finset (Fin s)) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact hk1' h1
    · exact hk12 h1
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := n) (K := K),
    Subgroup.closure_le]
  rintro A ⟨x, y, hxy, c, rfl⟩
  obtain ⟨a, i, rfl⟩ := hcoord x
  obtain ⟨b, j, rfl⟩ := hcoord y
  by_cases hij : i = j
  · subst j
    have hab : a ≠ b := fun h => hxy (by rw [h])
    obtain ⟨k, hki, hkne⟩ := hex i
    have hne_ki : ({k, i} : Finset (Fin s)) ≠ {i₀, j₀} := by
      simpa [Finset.pair_comm] using hkne
    let c0 : Fin (rootPB g).dim := ⟨0, by omega⟩
    have hA : SpecialLinearGroup.transvection
        (coord_inl_ne_coord_inl (ε := ε) hki.symm a c0) c ∈ H :=
      hcross i k hki.symm hkne a c0 c
    have hB : SpecialLinearGroup.transvection
        (coord_inl_ne_coord_inl (ε := ε) hki c0 b) (1 : K) ∈ H :=
      hcross k i hki hne_ki c0 b 1
    exact transvection_mem_of_three_index
      (coord_inl_ne_coord_inl (ε := ε) hki.symm a c0)
      (coord_inl_ne_coord_inl (ε := ε) hki c0 b)
      hxy c hA hB
  · by_cases hne : ({i, j} : Finset (Fin s)) = {i₀, j₀}
    · obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
      have hne_ik : ({i, k} : Finset (Fin s)) ≠ {i₀, j₀} := by
        intro h
        have hk : k ∈ ({i, j} : Finset (Fin s)) := by rw [hne, ← h]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with h1 | h1
        · exact hki h1
        · exact hkj h1
      have hne_kj : ({k, j} : Finset (Fin s)) ≠ {i₀, j₀} := by
        intro h
        have hk : k ∈ ({i, j} : Finset (Fin s)) := by rw [hne, ← h]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with h1 | h1
        · exact hki h1
        · exact hkj h1
      let c0 : Fin (rootPB g).dim := ⟨0, by omega⟩
      have hA : SpecialLinearGroup.transvection
          (coord_inl_ne_coord_inl (ε := ε) hki.symm a c0) c ∈ H :=
        hcross i k hki.symm hne_ik a c0 c
      have hB : SpecialLinearGroup.transvection
          (coord_inl_ne_coord_inl (ε := ε) hkj c0 b) (1 : K) ∈ H :=
        hcross k j hkj hne_kj c0 b 1
      exact transvection_mem_of_three_index
        (coord_inl_ne_coord_inl (ε := ε) hki.symm a c0)
        (coord_inl_ne_coord_inl (ε := ε) hkj c0 b)
        hxy c hA hB
    · have hres : SpecialLinearGroup.transvection
          (coord_inl_ne_coord_inl (ε := ε) hij a b) c ∈ H :=
        hcross i j hij hne a b c
      have hproof : SpecialLinearGroup.transvection hxy c =
          SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij a b) c :=
        Subtype.ext rfl
      rw [hproof]
      exact hres

end CFSG.StandardType.SlNsRootGen

end

module

public import CFSG.RankThree.PartOne.FOC.UnitaryFactor

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne
open scoped commutatorElement

universe u

section Numeric

theorem exists_pow_eq_of_not_dvd {G : Type*} [Monoid G] {δ : G} {p m : ℕ} (hp : p.Prime)
    (hδ : δ ^ p = 1) (hpm : ¬ p ∣ m) : ∃ r : ℕ, (δ ^ r) ^ m = δ := by
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨r, ?_⟩
  have h1 : r * m = p * (m * r / p) + 1 := by
    have := Nat.div_add_mod (m * r) p
    rw [hr] at this
    rw [mul_comm r m]
    omega
  rw [← pow_mul, h1, pow_add, pow_mul, hδ, one_pow, one_mul, pow_one]

end Numeric

section Scalars

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

@[expose] noncomputable def scalarGL (X : Module.End K V) (a : K[X]) (μ : (AdjoinRoot a)ˣ) :
    blockGL X a :=
  Units.map (algebraMap (AdjoinRoot a)
    (Module.End (AdjoinRoot a) (primaryComponent X a))).toMonoidHom μ

omit [FiniteDimensional K V] in
theorem blockApply_scalarGL (X : Module.End K V) (a : K[X]) (μ : (AdjoinRoot a)ˣ) (v : V)
    (hv : v ∈ primaryComponent X a) :
    blockApply (scalarGL X a μ) v hv =
      (((μ : AdjoinRoot a) • (⟨v, hv⟩ : primaryComponent X a) : primaryComponent X a) : V) := by
  simp [blockApply, scalarGL, Module.algebraMap_end_apply]

theorem det_scalarGL (X : Module.End K V) (a : primaryFactors X) (μ : (AdjoinRoot (a : K[X]))ˣ) :
    LinearMap.det ((scalarGL X (a : K[X]) μ : blockGL X (a : K[X])) :
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent X (a : K[X]))) =
      (μ : AdjoinRoot (a : K[X])) ^ primaryMultiplicity X (a : K[X]) := by
  have : (((scalarGL X (a : K[X]) μ : blockGL X (a : K[X])) :
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent X (a : K[X]))) =
      (μ : AdjoinRoot (a : K[X])) • (1 : Module.End (AdjoinRoot (a : K[X]))
        (primaryComponent X (a : K[X])))) := by
    simp [scalarGL, Algebra.algebraMap_eq_smul_one]
  rw [this, LinearMap.det_smul, Module.End.one_eq_id, LinearMap.det_id, mul_one]

end Scalars

section Split

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

@[expose] def HasScalar (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (x : LinearMap.GeneralLinearGroup K V)
    (a : K[X]) (μ : AdjoinRoot a) : Prop :=
  ∃ z ∈ orbitFactor B x a, ∀ v : primaryComponent (x : Module.End K V) a,
    ((z : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
      ((μ • v : primaryComponent (x : Module.End K V) a) : V)

theorem splits_of_hasScalar (a : primaryFactors (x : Module.End K V)) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ orbitFactor B x (a : K[X])) {μ : (AdjoinRoot (a : K[X]))ˣ}
    (hμ : HasScalar B x (a : K[X]) (μ : AdjoinRoot (a : K[X])))
    (hdet : blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ =
      μ ^ primaryMultiplicity (x : Module.End K V) (a : K[X])) :
    ∃ z ∈ orbitFactor B x (a : K[X]),
      (∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        ((z : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V)) ∧
      z⁻¹ * g ∈ specialBlock B x (a : K[X]) := by
  obtain ⟨z, hz, hzact⟩ := hμ
  refine ⟨z, hz, ⟨(μ : AdjoinRoot (a : K[X])), hzact⟩, ?_⟩
  have hzc : z ∈ gl_centralizer x := orbitFactor_le_gl_centralizer hz
  have hres : blockRestrict x (a : K[X]) ⟨z, hzc⟩ = scalarGL (x : Module.End K V) (a : K[X]) μ := by
    refine blockGL_ext fun v hv => ?_
    rw [blockApply_blockRestrict, blockApply_scalarGL]
    exact hzact ⟨v, hv⟩
  have hdz : blockDetHom x (a : K[X]) ⟨z, hzc⟩ =
      μ ^ primaryMultiplicity (x : Module.End K V) (a : K[X]) := by
    apply Units.ext
    change LinearMap.det ((blockRestrict x (a : K[X]) ⟨z, hzc⟩ : blockGL (x : Module.End K V)
      (a : K[X])) : Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V)
        (a : K[X]))) = _
    rw [hres, det_scalarGL]
    simp
  rw [mem_specialBlock]
  refine ⟨mul_mem (inv_mem hz) hg, mul_mem (inv_mem hzc) (orbitFactor_le_gl_centralizer hg), ?_⟩
  have : (⟨z⁻¹ * g, mul_mem (inv_mem hzc) (orbitFactor_le_gl_centralizer hg)⟩ :
      gl_centralizer x) = ⟨z, hzc⟩⁻¹ * ⟨g, orbitFactor_le_gl_centralizer hg⟩ := rfl
  rw [this, map_mul, map_inv, hdz, hdet, inv_mul_cancel]

variable (H : UnitaryPrimaryData hK.bar B x)
include H

omit H in
theorem hasScalar_paired {a : primaryFactors (x : Module.End K V)}
    (hP : PairedPrimaryBlock hK B x a) (μ : (AdjoinRoot (a : K[X]))ˣ) :
    HasScalar B x (a : K[X]) (μ : AdjoinRoot (a : K[X])) := by
  obtain ⟨φ, hφ, -⟩ := exists_pairedFactor hP
  refine ⟨(φ.symm (scalarGL (x : Module.End K V) (a : K[X]) μ) :
    LinearMap.GeneralLinearGroup K V), (φ.symm _).2, fun v => ?_⟩
  have h1 := hφ (φ.symm (scalarGL (x : Module.End K V) (a : K[X]) μ)) v.1 v.2
  rw [MulEquiv.apply_symm_apply, blockApply_scalarGL] at h1
  exact h1.symm

omit H in
theorem exists_scalar_paired {a : primaryFactors (x : Module.End K V)}
    (hP : PairedPrimaryBlock hK B x a) {p : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ primaryMultiplicity (x : Module.End K V) (a : K[X]))
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ orbitFactor B x (a : K[X])) (hgp : g ^ p = 1) :
    ∃ μ : (AdjoinRoot (a : K[X]))ˣ, HasScalar B x (a : K[X]) (μ : AdjoinRoot (a : K[X])) ∧
      blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ =
        μ ^ primaryMultiplicity (x : Module.End K V) (a : K[X]) := by
  have hδp : (blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨g, orbitFactor_le_gl_centralizer hg⟩ : gl_centralizer x) ^ p = 1 :=
      Subtype.ext (by simpa using hgp)
    rw [this, map_one]
  obtain ⟨r, hr⟩ := exists_pow_eq_of_not_dvd hp hδp hpm
  exact ⟨_, hasScalar_paired hP _, hr.symm⟩

omit H in
theorem exists_scalar_selfDual {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a) {p : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ primaryMultiplicity (x : Module.End K V) (a : K[X]))
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ orbitFactor B x (a : K[X])) (hgp : g ^ p = 1) :
    ∃ μ : (AdjoinRoot (a : K[X]))ˣ, HasScalar B x (a : K[X]) (μ : AdjoinRoot (a : K[X])) ∧
      blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ =
        μ ^ primaryMultiplicity (x : Module.End K V) (a : K[X]) := by
  obtain ⟨hE, -, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ₀, hφ₀, -⟩ := hS.unitaryForm
  have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} :=
    orbitFactor_eq_supportedUnitary_of_selfDual hself
  let φ : orbitFactor B x (a : K[X]) ≃* sesqUnitaryGroup Hf :=
    (MulEquiv.subgroupCongr hsupp).trans φ₀
  have hφact : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
    fun g v hv => hφ₀ ((MulEquiv.subgroupCongr hsupp) g) v hv
  set δ := blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ with hδ
  have hδp : δ ^ p = 1 := by
    rw [hδ, ← map_pow]
    have : (⟨g, orbitFactor_le_gl_centralizer hg⟩ : gl_centralizer x) ^ p = 1 :=
      Subtype.ext (by simpa using hgp)
    rw [this, map_one]
  obtain ⟨r, hr⟩ := exists_pow_eq_of_not_dvd hp hδp hpm
  have hres : blockRestrict x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ =
      (φ ⟨g, hg⟩ : blockGL (x : Module.End K V) (a : K[X])) := by
    refine blockGL_ext fun v hv => ?_
    rw [blockApply_blockRestrict, hφact ⟨g, hg⟩ v hv]
  have hnδ : hE.norm (δ : AdjoinRoot (a : K[X])) = 1 := by
    have h1 : (δ : AdjoinRoot (a : K[X])) = LinearMap.det ((φ ⟨g, hg⟩ : blockGL
        (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) := by
      rw [hδ]
      change LinearMap.det ((blockRestrict x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ :
        blockGL (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) = _
      rw [hres]
    rw [h1]
    exact CFSG.LinearGroups.norm_det_of_isometry hE e
      (CFSG.LinearGroups.mem_orthonormalFrames.mpr he)
      (fun v w => mem_sesqUnitaryGroup.mp (φ ⟨g, hg⟩).2 v w)
  have hnμ : hE.norm (((δ ^ r : (AdjoinRoot (a : K[X]))ˣ) : AdjoinRoot (a : K[X]))) = 1 := by
    rw [Units.val_pow_eq_pow_val]
    unfold UnitaryFieldData.norm at hnδ ⊢
    rw [map_pow, ← mul_pow, hnδ, one_pow]
  have hmem : scalarGL (x : Module.End K V) (a : K[X]) (δ ^ r) ∈ sesqUnitaryGroup Hf := by
    rw [mem_sesqUnitaryGroup]
    intro v w
    have hsc : ∀ (μ : (AdjoinRoot (a : K[X]))ˣ) (u : primaryComponent (x : Module.End K V)
        (a : K[X])), ((scalarGL (x : Module.End K V) (a : K[X]) μ : blockGL (x : Module.End K V)
          (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))) u =
          (μ : AdjoinRoot (a : K[X])) • u := by
      intro μ u
      simp [scalarGL, Module.algebraMap_end_apply]
    rw [hsc, hsc]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h1 := hnμ
    unfold UnitaryFieldData.norm at h1
    linear_combination (Hf v w) * h1
  refine ⟨δ ^ r, ⟨(φ.symm ⟨scalarGL (x : Module.End K V) (a : K[X]) (δ ^ r), hmem⟩ :
    LinearMap.GeneralLinearGroup K V), (φ.symm _).2, fun v => ?_⟩, hr.symm⟩
  have h1 := hφact (φ.symm ⟨scalarGL (x : Module.End K V) (a : K[X]) (δ ^ r), hmem⟩) v.1 v.2
  rw [MulEquiv.apply_symm_apply] at h1
  change blockApply (scalarGL (x : Module.End K V) (a : K[X]) (δ ^ r)) v.1 v.2 = _ at h1
  rw [blockApply_scalarGL] at h1
  exact h1.symm

theorem goodSplit_of_det {p : ℕ} (hp : p.Prime)
    (hrk : ∀ a : primaryFactors (x : Module.End K V), IsGoodBlock hK x a →
      p ∣ primaryMultiplicity (x : Module.End K V) (a : K[X]) →
      ∀ (g : LinearMap.GeneralLinearGroup K V) (hg : g ∈ orbitFactor B x (a : K[X])), g ^ p = 1 →
        blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ = 1) :
    GoodSplit hK B x p := by
  intro a hgood g hg hgp
  by_cases hpm : p ∣ primaryMultiplicity (x : Module.End K V) (a : K[X])
  · have h1 := hrk a hgood hpm g hg hgp
    refine splits_of_hasScalar a hg (μ := 1) ⟨1, one_mem _, fun v => ?_⟩ ?_
    · simp
    · rw [h1]
      simp
  · by_cases hself : dualPoly hK.bar (a : K[X]) = a
    · obtain ⟨μ, hμ, hd⟩ := exists_scalar_selfDual hself (selfDualPrimaryBlock H a hself) hp hpm
        hg hgp
      exact splits_of_hasScalar a hg hμ hd
    · obtain ⟨μ, hμ, hd⟩ := exists_scalar_paired (pairedPrimaryBlock H a (Ne.symm hself)) hp hpm
        hg hgp
      exact splits_of_hasScalar a hg hμ hd

omit H in
theorem selfDual_det_pow {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ orbitFactor B x (a : K[X])) :
    ((blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ :
      (AdjoinRoot (a : K[X]))ˣ) : AdjoinRoot (a : K[X])) ^
        ((ℓ ^ f) ^ (a : K[X]).natDegree + 1) = 1 := by
  obtain ⟨hE, hbar, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ₀, hφ₀, -⟩ := hS.unitaryForm
  have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} :=
    orbitFactor_eq_supportedUnitary_of_selfDual hself
  let φ : orbitFactor B x (a : K[X]) ≃* sesqUnitaryGroup Hf :=
    (MulEquiv.subgroupCongr hsupp).trans φ₀
  have hφact : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
    fun g v hv => hφ₀ ((MulEquiv.subgroupCongr hsupp) g) v hv
  have hres : blockRestrict x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ =
      (φ ⟨g, hg⟩ : blockGL (x : Module.End K V) (a : K[X])) := by
    refine blockGL_ext fun v hv => ?_
    rw [blockApply_blockRestrict, hφact ⟨g, hg⟩ v hv]
  have h1 : ((blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ :
      (AdjoinRoot (a : K[X]))ˣ) : AdjoinRoot (a : K[X])) =
      LinearMap.det ((φ ⟨g, hg⟩ : blockGL (x : Module.End K V) (a : K[X])) :
        Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) := by
    change LinearMap.det ((blockRestrict x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ :
      blockGL (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) = _
    rw [hres]
  have hn : hE.norm ((blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ :
      (AdjoinRoot (a : K[X]))ˣ) : AdjoinRoot (a : K[X])) = 1 := by
    rw [h1]
    exact CFSG.LinearGroups.norm_det_of_isometry hE e
      (CFSG.LinearGroups.mem_orthonormalFrames.mpr he)
      (fun v w => mem_sesqUnitaryGroup.mp (φ ⟨g, hg⟩).2 v w)
  unfold UnitaryFieldData.norm at hn
  rw [hbar, ← pow_succ'] at hn
  exact hn

end Split

end CFSG.RankThree.PartOne.FOC

module

public import CFSG.RankThree.PartOne.FOC.UnitaryFactorAll
public import CFSG.RankThree.PartOne.FOC.UnitarySplit

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne

universe u

section Numeric

theorem exists_pow_eq_of_coprime {G : Type*} [Monoid G] {δ : G} {n m : ℕ} (hδ : δ ^ n = 1)
    (hn : 1 < n) (hcop : Nat.Coprime m n) : ∃ r : ℕ, (δ ^ r) ^ m = δ := by
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn
  refine ⟨r, ?_⟩
  have h1 : r * m = n * (m * r / n) + 1 := by
    have := Nat.div_add_mod (m * r) n
    rw [hr] at this
    rw [mul_comm r m]
    omega
  rw [← pow_mul, h1, pow_add, pow_mul, hδ, one_pow, one_mul, pow_one]

end Numeric

section Split

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem exists_scalar_selfDual_of_root {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ orbitFactor B x (a : K[X]))
    (hroot : ∃ r : ℕ, ((blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩) ^ r) ^
      primaryMultiplicity (x : Module.End K V) (a : K[X]) =
        blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩) :
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
  obtain ⟨r, hr⟩ := hroot
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

variable (H : UnitaryPrimaryData hK.bar B x)
include H

theorem goodSplitAll_of_coprime
    (hsd : ∀ a : primaryFactors (x : Module.End K V), IsGoodBlock hK x a →
      dualPoly hK.bar (a : K[X]) = a ∧
        Nat.Coprime (primaryMultiplicity (x : Module.End K V) (a : K[X]))
          ((ℓ ^ f) ^ (a : K[X]).natDegree + 1)) (hq : 2 ≤ ℓ ^ f) :
    GoodSplitAll hK B x := by
  intro a hgood g hg
  obtain ⟨hself, hcop⟩ := hsd a hgood
  have hS := selfDualPrimaryBlock H a hself
  have hδN : ((blockDetHom x (a : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ :
      (AdjoinRoot (a : K[X]))ˣ)) ^ ((ℓ ^ f) ^ (a : K[X]).natDegree + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact selfDual_det_pow hself hS hg
  have hn : 1 < (ℓ ^ f) ^ (a : K[X]).natDegree + 1 := by
    have h1 : 1 ≤ (ℓ ^ f) ^ (a : K[X]).natDegree := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨r, hr⟩ := exists_pow_eq_of_coprime hδN hn hcop
  obtain ⟨μ, hμ, hd⟩ := exists_scalar_selfDual_of_root hself hS hg ⟨r, hr⟩
  exact splits_of_hasScalar a hg hμ hd

end Split

end CFSG.RankThree.PartOne.FOC

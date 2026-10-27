module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeBlocks

public section

namespace CFSG.RankThree.PartOne.KCUnitaryTransvection

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {hK : UnitaryFieldData ℓ f K} {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem exists_mem_specialBlock_of_blockGL (H : UnitaryPrimaryData hK.bar B x) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hne : a ≠ dualPoly hK.bar a)
    [Fact (Irreducible a)] (γ₀ : blockGL (x : Module.End K V) a)
    (hdet : LinearMap.det (γ₀ : Module.End (AdjoinRoot a) (primaryComponent
      (x : Module.End K V) a)) = 1) :
    ∃ g ∈ specialBlock B x a, ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      (g : Module.End K V) v = blockApply γ₀ v hv := by
  obtain ⟨g, hg⟩ := supportedRestrict_surjective_of_paired H ha hne γ₀
  have hgc : (g : LinearMap.GeneralLinearGroup K V) ∈ gl_centralizer x :=
    supportedUnitary_le_gl_centralizer _ g.2
  have hval : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply γ₀ v hv := by
    intro v hv
    rw [← coe_supportedRestrict H _ ⟨a, ha⟩ g ⟨v, hv⟩, hg]
    rfl
  refine ⟨g, mem_specialBlock.mpr ⟨g.2, hgc, ?_⟩, hval⟩
  have hrestr : blockRestrict x a ⟨g, hgc⟩ = γ₀ :=
    blockGL_ext (fun v hv => by rw [blockApply_blockRestrict]; exact hval v hv)
  rw [blockDetHom, MonoidHom.comp_apply, hrestr]
  apply Units.ext
  rw [blockGLDet, Units.coe_map]
  exact hdet

theorem exists_mem_specialBlock_transvection (H : UnitaryPrimaryData hK.bar B x) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hne : a ≠ dualPoly hK.bar a)
    [Fact (Irreducible a)]
    (φ : Module.Dual (AdjoinRoot a) (primaryComponent (x : Module.End K V) a))
    (u : primaryComponent (x : Module.End K V) a) (hφ : φ u = 0) :
    ∃ g ∈ specialBlock B x a, ∀ (y : V) (hy : y ∈ primaryComponent (x : Module.End K V) a),
      (g : Module.End K V) y =
        y + ((φ ⟨y, hy⟩ • u : primaryComponent (x : Module.End K V) a) : V) := by
  let γ₀ : blockGL (x : Module.End K V) a :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hφ)
  have hdet : LinearMap.det (γ₀ : Module.End (AdjoinRoot a) (primaryComponent
      (x : Module.End K V) a)) = 1 := by
    have h1 : LinearMap.det ((LinearEquiv.transvection hφ : primaryComponent
        (x : Module.End K V) a ≃ₗ[AdjoinRoot a] primaryComponent (x : Module.End K V) a) :
          primaryComponent (x : Module.End K V) a →ₗ[AdjoinRoot a]
            primaryComponent (x : Module.End K V) a) = 1 := by
      rw [← LinearEquiv.coe_det, LinearEquiv.transvection.det_eq_one hφ, Units.val_one]
    exact h1
  obtain ⟨g, hg, hval⟩ := exists_mem_specialBlock_of_blockGL H ha hne γ₀ hdet
  refine ⟨g, hg, fun y hy => ?_⟩
  rw [hval y hy]
  rfl

end CFSG.RankThree.PartOne.KCUnitaryTransvection

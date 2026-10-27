module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryCentralizer

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G] (Sup : Subgroup G) {Ω : Type*} [Group Ω] {A : Type*}
  [CommGroup A] (φ : Sup ≃* Ω) (D : Ω →* A)

@[expose] def kerImage : Subgroup G := ((D.comp φ.toMonoidHom).ker).map Sup.subtype

theorem mem_kerImage {g : G} : g ∈ kerImage Sup φ D ↔ ∃ hg : g ∈ Sup, D (φ ⟨g, hg⟩) = 1 := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem kerImage_le : kerImage Sup φ D ≤ Sup := by
  rintro g hg
  exact ((mem_kerImage Sup φ D).mp hg).1

theorem commutator_le_kerImage : ⁅Sup, Sup⁆ ≤ kerImage Sup φ D := by
  refine Subgroup.commutator_le.mpr fun g hg g' hg' => ?_
  have hmem : ⁅g, g'⁆ ∈ Sup := commutator_self_le Sup (Subgroup.commutator_mem_commutator hg hg')
  refine (mem_kerImage Sup φ D).mpr ⟨hmem, ?_⟩
  have : (⟨⁅g, g'⁆, hmem⟩ : Sup) = ⁅(⟨g, hg⟩ : Sup), ⟨g', hg'⟩⁆ := rfl
  rw [this, map_commutatorElement, map_commutatorElement, commutatorElement_def, mul_comm (D _),
    mul_inv_cancel_right, mul_inv_cancel]

theorem nonempty_kerImage_mulEquiv : Nonempty (kerImage Sup φ D ≃* D.ker) := by
  have h1 : (kerImage Sup φ D) = ((D.comp φ.toMonoidHom).ker).map Sup.subtype := rfl
  let e1 : (D.comp φ.toMonoidHom).ker ≃* (kerImage Sup φ D) :=
    ((D.comp φ.toMonoidHom).ker).equivMapOfInjective Sup.subtype Subtype.val_injective
  have hmap : ((D.comp φ.toMonoidHom).ker).map φ.toMonoidHom = D.ker := by
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hw
      refine ⟨φ.symm w, ?_, by simp⟩
      change D (φ (φ.symm w)) = 1
      rw [MulEquiv.apply_symm_apply]
      exact hw
  exact ⟨e1.symm.trans (((φ.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)))⟩

theorem kerImage_eq_commutator (hperf : Group.IsPerfect D.ker) :
    kerImage Sup φ D = ⁅Sup, Sup⁆ := by
  apply le_antisymm _ (commutator_le_kerImage Sup φ D)
  obtain ⟨e⟩ := nonempty_kerImage_mulEquiv Sup φ D
  have hF : Group.IsPerfect (kerImage Sup φ D) :=
    @isPerfect_of_surjective _ _ _ _ e.symm.toMonoidHom e.symm.surjective hperf
  calc kerImage Sup φ D = ⁅kerImage Sup φ D, kerImage Sup φ D⁆ :=
        (commutator_eq_of_isPerfect hF).symm
    _ ≤ ⁅Sup, Sup⁆ := Subgroup.commutator_mono (kerImage_le Sup φ D) (kerImage_le Sup φ D)

theorem exists_mem_kerImage {δ : Ω} (hδ : D δ = 1) :
    ∃ g ∈ kerImage Sup φ D, ∃ hg : g ∈ Sup, φ ⟨g, hg⟩ = δ := by
  refine ⟨((φ.symm δ : Sup) : G), ?_, (φ.symm δ).2, ?_⟩
  · refine (mem_kerImage Sup φ D).mpr ⟨(φ.symm δ).2, ?_⟩
    simpa using hδ
  · simp

end Abstract

section Defs

universe u

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] {σ : K →+* K}

@[expose] noncomputable def blockRestrict (x : LinearMap.GeneralLinearGroup K V) (a : K[X]) :
    gl_centralizer x →* blockGL (x : Module.End K V) a :=
  (Units.map (commutantRestrictHom (x := (x : Module.End K V)) a).toMonoidHom).comp
    (glCentralizerEquivUnits x).toMonoidHom

theorem blockApply_blockRestrict (x : LinearMap.GeneralLinearGroup K V) (a : K[X])
    (g : gl_centralizer x) (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a) :
    blockApply (blockRestrict x a g) v hv =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := rfl

theorem blockGL_ext {x : Module.End K V} {a : K[X]} {γ γ' : blockGL x a}
    (h : ∀ (v : V) (hv : v ∈ primaryComponent x a), blockApply γ v hv = blockApply γ' v hv) :
    γ = γ' :=
  Units.ext (LinearMap.ext fun v => Subtype.ext (h v.1 v.2))

@[expose] noncomputable def blockGLDet (x : Module.End K V) (a : K[X]) :
    blockGL x a →* (AdjoinRoot a)ˣ :=
  Units.map (LinearMap.det : Module.End (AdjoinRoot a) (primaryComponent x a) →* AdjoinRoot a)

@[expose] noncomputable def blockDetHom (x : LinearMap.GeneralLinearGroup K V) (a : K[X]) :
    gl_centralizer x →* (AdjoinRoot a)ˣ :=
  (blockGLDet (x : Module.End K V) a).comp (blockRestrict x a)

@[expose] def orbitFactor (B : V →ₛₗ[σ] V →ₗ[K] K) (x : LinearMap.GeneralLinearGroup K V)
    (a : K[X]) : Subgroup (LinearMap.GeneralLinearGroup K V) :=
  supportedUnitary B x {a, dualPoly σ a}

@[expose] noncomputable def specialBlock (B : V →ₛₗ[σ] V →ₗ[K] K)
    (x : LinearMap.GeneralLinearGroup K V) (a : K[X]) :
    Subgroup (LinearMap.GeneralLinearGroup K V) :=
  orbitFactor B x a ⊓ (blockDetHom x a).ker.map (gl_centralizer x).subtype

variable {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V} {a : K[X]}

theorem mem_specialBlock {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ specialBlock B x a ↔ g ∈ orbitFactor B x a ∧
      ∃ hg : g ∈ gl_centralizer x, blockDetHom x a ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨hs, ⟨y, hy, rfl⟩⟩
    exact ⟨hs, y.2, hy⟩
  · rintro ⟨hs, hg, h⟩
    exact ⟨hs, ⟨g, hg⟩, h, rfl⟩

theorem specialBlock_le_orbitFactor : specialBlock B x a ≤ orbitFactor B x a := inf_le_left

theorem orbitFactor_le_unitaryCentralizer : orbitFactor B x a ≤ unitaryCentralizer B x :=
  supportedUnitary_le_unitaryCentralizer _

theorem orbitFactor_le_gl_centralizer : orbitFactor B x a ≤ gl_centralizer x :=
  supportedUnitary_le_gl_centralizer _

theorem specialBlock_le_unitaryCentralizer : specialBlock B x a ≤ unitaryCentralizer B x :=
  specialBlock_le_orbitFactor.trans orbitFactor_le_unitaryCentralizer

theorem conj_mem_supportedUnitary {S : Set K[X]} {m g : LinearMap.GeneralLinearGroup K V}
    (hm : m ∈ unitaryCentralizer B x) (hg : g ∈ supportedUnitary B x S) :
    m * g * m⁻¹ ∈ supportedUnitary B x S := by
  refine ⟨mul_mem (mul_mem hm hg.1) (inv_mem hm), fun b hb hbS v hv => ?_⟩
  have hc : Commute (((m⁻¹ : LinearMap.GeneralLinearGroup K V)) : Module.End K V)
      (x : Module.End K V) := mem_gl_centralizer.mp (inv_mem hm).2
  have h1 := apply_mem_primaryComponent hc hv
  have h2 := hg.2 b hb hbS _ h1
  change (m : Module.End K V) ((g : Module.End K V) (((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
    Module.End K V) v)) = v
  rw [h2, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
  rfl

theorem conj_mem_specialBlock {m g : LinearMap.GeneralLinearGroup K V}
    (hm : m ∈ unitaryCentralizer B x) (hg : g ∈ specialBlock B x a) :
    m * g * m⁻¹ ∈ specialBlock B x a := by
  obtain ⟨hs, hgc, hdet⟩ := mem_specialBlock.mp hg
  refine mem_specialBlock.mpr ⟨conj_mem_supportedUnitary hm hs,
    mul_mem (mul_mem hm.2 hgc) (inv_mem hm.2), ?_⟩
  have : (⟨m * g * m⁻¹, mul_mem (mul_mem hm.2 hgc) (inv_mem hm.2)⟩ : gl_centralizer x) =
      ⟨m, hm.2⟩ * ⟨g, hgc⟩ * ⟨m, hm.2⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hdet, mul_one, mul_comm, inv_mul_cancel]

end Defs

end CFSG.RankThree.PartOne.KCUnitary

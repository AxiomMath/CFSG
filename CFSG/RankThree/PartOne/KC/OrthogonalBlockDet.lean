module

public import CFSG.RankThree.PartOne.KC.OrthogonalPairedBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Defs

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] noncomputable def centralizerDet (x : V ≃ₗ[K] V) (h : K[X]) :
    ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) →* AdjoinRoot h :=
  (LinearMap.det : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h) →*
      AdjoinRoot h).comp ((Units.coeHom _).comp (centralizerGL x h))

@[expose] noncomputable def blockDet (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) :
    ↥(supportedBlock Q x h) →* AdjoinRoot h :=
  (centralizerDet x h).comp (Subgroup.inclusion (supportedBlock_le_centralizer h))

theorem blockDet_apply (h : K[X]) (g : ↥(supportedBlock Q x h)) :
    blockDet Q x h g = LinearMap.det ((blockGL Q x h g : BlockGL x h) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) := rfl

@[expose] noncomputable def specialBlock (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) :
    Subgroup (V ≃ₗ[K] V) :=
  (blockDet Q x h).ker.map (supportedBlock Q x h).subtype

theorem mem_specialBlock {g : V ≃ₗ[K] V} {h : K[X]} :
    g ∈ specialBlock Q x h ↔ ∃ hg : g ∈ supportedBlock Q x h, blockDet Q x h ⟨g, hg⟩ = 1 := by
  simp only [specialBlock, Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype]
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem specialBlock_le_supportedBlock (h : K[X]) :
    specialBlock Q x h ≤ supportedBlock Q x h := fun _ hg => (mem_specialBlock.mp hg).1

theorem specialBlock_le_isometryCentralizer (h : K[X]) :
    specialBlock Q x h ≤ isometryCentralizer Q x :=
  (specialBlock_le_supportedBlock h).trans (supportedBlock_le_isometryCentralizer h)

theorem blockDet_eq_one_of_mem_specialBlock {g : V ≃ₗ[K] V} {h : K[X]}
    (hg : g ∈ specialBlock Q x h) :
    blockDet Q x h ⟨g, specialBlock_le_supportedBlock h hg⟩ = 1 := by
  obtain ⟨hg', h1⟩ := mem_specialBlock.mp hg
  exact h1

theorem conj_mem_specialBlock {g f : V ≃ₗ[K] V} {h : K[X]} (hg : g ∈ isometryCentralizer Q x)
    (hf : f ∈ specialBlock Q x h) : g * f * g⁻¹ ∈ specialBlock Q x h := by
  obtain ⟨hfS, hfd⟩ := mem_specialBlock.mp hf
  have hgc : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hg).2
  have hgc' : g⁻¹ ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := inv_mem hgc
  have hfc : f ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    supportedBlock_le_centralizer h hfS
  have hS : g * f * g⁻¹ ∈ supportedBlock Q x h := by
    refine mem_supportedBlock.mpr ⟨mul_mem (mul_mem hg
      (supportedBlock_le_isometryCentralizer h hfS)) (inv_mem hg), fun r hr => ?_⟩
    have hr' : g⁻¹ r ∈ othersSpace x.toLinearMap h := mem_othersSpace_of_apply hgc' hr
    show g (f (g⁻¹ r)) = r
    rw [(mem_supportedBlock.mp hfS).2 _ hr']
    exact g.apply_symm_apply r
  refine mem_specialBlock.mpr ⟨hS, ?_⟩
  have h1 : (⟨g * f * g⁻¹, supportedBlock_le_centralizer h hS⟩ :
      ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))) = ⟨g, hgc⟩ * ⟨f, hfc⟩ * ⟨g, hgc⟩⁻¹ := rfl
  show centralizerDet x h ⟨g * f * g⁻¹, supportedBlock_le_centralizer h hS⟩ = 1
  have hf1 : centralizerDet x h ⟨f, hfc⟩ = 1 := hfd
  rw [h1, map_mul, map_mul, hf1, mul_one, ← map_mul, mul_inv_cancel, map_one]

section Special

variable [FiniteDimensional K V]

@[expose] noncomputable def specialBlockGL (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) :
    ↥(specialBlock Q x h) →* BlockGL x h :=
  (blockGL Q x h).comp (Subgroup.inclusion (specialBlock_le_supportedBlock h))

omit [FiniteDimensional K V] in
theorem det_specialBlockGL (h : K[X]) (g : ↥(specialBlock Q x h)) :
    LinearMap.det ((specialBlockGL Q x h g : BlockGL x h) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) = 1 :=
  blockDet_eq_one_of_mem_specialBlock g.2

@[expose] noncomputable def specialToSL (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) :
    ↥(specialBlock Q x h) →*
      SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) where
  toFun g := ⟨(specialBlockGL Q x h g).toLinearEquiv, Units.ext (by
    rw [LinearEquiv.coe_det]
    exact det_specialBlockGL h g)⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (LinearEquiv.ext fun _ => rfl)

omit [FiniteDimensional K V] in
theorem specialToSL_apply (h : K[X]) (g : ↥(specialBlock Q x h))
    (v : primaryComponent x.toLinearMap h) :
    (((specialToSL Q x h g : SpecialLinearGroup (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) : primaryComponent x.toLinearMap h ≃ₗ[AdjoinRoot h]
        primaryComponent x.toLinearMap h) v : V) = g.1 (v : V) := rfl

theorem OddOrderIsometry.specialToSL_injective (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) : Function.Injective (specialToSL Q x h) := by
  intro g g' hgg
  have hv : ∀ v : primaryComponent x.toLinearMap h, g.1 (v : V) = g'.1 (v : V) := fun v => by
    have := congrArg (fun e : SpecialLinearGroup (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) =>
      ((e : primaryComponent x.toLinearMap h ≃ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h)
        v : V)) hgg
    exact this
  have hinj := hx.blockGL_injective hh
  have h2 : (⟨g.1, specialBlock_le_supportedBlock h g.2⟩ : ↥(supportedBlock Q x h)) =
      ⟨g'.1, specialBlock_le_supportedBlock h g'.2⟩ :=
    hinj (Units.ext (LinearMap.ext fun v => Subtype.ext (hv v)))
  have h3 : g.1 = g'.1 := congrArg (fun y : ↥(supportedBlock Q x h) => y.1) h2
  exact Subtype.ext h3

theorem OddOrderIsometry.specialBlock_eq_bot_of_finrank_eq_one (hx : OddOrderIsometry Q p x)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (h1 : primaryMultiplicity x.toLinearMap h = 1) : specialBlock Q x h = ⊥ := by
  have : Subsingleton (SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :=
    SpecialLinearGroup.subsingleton_of_finrank_eq_one h1
  have : Subsingleton ↥(specialBlock Q x h) := (hx.specialToSL_injective hh).subsingleton
  exact Subgroup.eq_bot_of_subsingleton _

end Special

section Scalars

@[expose] noncomputable def scalarGL (x : V ≃ₗ[K] V) (h : K[X]) (c : (AdjoinRoot h)ˣ) :
    BlockGL x h :=
  Units.map (algebraMap (AdjoinRoot h)
    (Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))).toMonoidHom c

theorem coe_scalarGL (h : K[X]) (c : (AdjoinRoot h)ˣ) (v : primaryComponent x.toLinearMap h) :
    ((scalarGL x h c : BlockGL x h) : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) v = (c : AdjoinRoot h) • v := rfl

theorem scalarGL_mul (h : K[X]) (c d : (AdjoinRoot h)ˣ) :
    scalarGL x h (c * d) = scalarGL x h c * scalarGL x h d := by
  simp [scalarGL]

theorem scalarGL_pow (h : K[X]) (c : (AdjoinRoot h)ˣ) (n : ℕ) :
    scalarGL x h (c ^ n) = scalarGL x h c ^ n := by
  simp [scalarGL]

theorem scalarGL_one (h : K[X]) : scalarGL x h 1 = 1 := by
  simp [scalarGL]

theorem scalarGL_injective (h : K[X]) (hne : primaryComponent x.toLinearMap h ≠ ⊥)
    [Fact (Irreducible h)] : Function.Injective (scalarGL x h) := by
  intro c d hcd
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h1 := congrArg (fun γ : BlockGL x h => ((γ : Module.End (AdjoinRoot h)
    (primaryComponent x.toLinearMap h)) ⟨v, hv⟩)) hcd
  simp only [coe_scalarGL] at h1
  have h2 : ((c : AdjoinRoot h) - d) • (⟨v, hv⟩ : primaryComponent x.toLinearMap h) = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact Units.ext (sub_eq_zero.mp h3)
  · exact absurd (congrArg Subtype.val h3) hv0

theorem scalarGL_mem_center (h : K[X]) (c : (AdjoinRoot h)ˣ) :
    scalarGL x h c ∈ Subgroup.center (BlockGL x h) := by
  rw [Subgroup.mem_center_iff]
  intro g
  refine Units.ext ?_
  show (g : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) *
    algebraMap (AdjoinRoot h) (Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))
      (c : AdjoinRoot h) = _
  exact (Algebra.commutes (c : AdjoinRoot h) _).symm

theorem det_scalarGL (h : K[X]) [Fact (Irreducible h)] (c : (AdjoinRoot h)ˣ) :
    LinearMap.det ((scalarGL x h c : BlockGL x h) : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) =
      (c : AdjoinRoot h) ^ primaryMultiplicity x.toLinearMap h := by
  have : ((scalarGL x h c : BlockGL x h) : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) = (c : AdjoinRoot h) • LinearMap.id := rfl
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

end Scalars

end Defs

end CFSG.RankThree.PartOne.KCOrthogonal

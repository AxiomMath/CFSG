module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6Core
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6Tw
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace MpStdTwE6

section BaseChange

variable
  {F K : Type} [Field F] [Field K] (τ : F ≃+* K) {θ : F →+* F} {σ : K →+* K}

theorem baseChangeGL_twistHom (hτ : τ.toRingHom.comp θ = σ.comp τ.toRingHom) (t : TwistTag)
    (g : ModGL t.tag F) :
    baseChangeGL τ.toRingHom (twistHom t F θ g) =
      twistHom t K σ (baseChangeGL τ.toRingHom g) := by
  rw [twistHom_apply, twistHom_apply, units_map_entrywiseHom_eq_baseChangeGL,
    units_map_entrywiseHom_eq_baseChangeGL, map_mul, map_mul, map_inv,
    baseChangeGL_diagramMap, baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hτ]

theorem baseChangeGL_mem_twistedFixedGroup_of_comp
    (hτ : τ.toRingHom.comp θ = σ.comp τ.toRingHom) (t : TwistTag) {g : ModGL t.tag F}
    (hg : g ∈ twistedFixedGroup t F θ) :
    baseChangeGL τ.toRingHom g ∈ twistedFixedGroup t K σ := by
  obtain ⟨hgC, hgF⟩ := (mem_twistedFixedGroup_iff_twistHom t F θ).1 hg
  refine (mem_twistedFixedGroup_iff_twistHom t K σ).2
    ⟨baseChangeGL_mem_adjointGroup _ hgC, ?_⟩
  rw [← baseChangeGL_twistHom τ hτ, hgF]

theorem map_derived_le (hτ : τ.toRingHom.comp θ = σ.comp τ.toRingHom) (t : TwistTag) :
    (⁅twistedFixedGroup t F θ, twistedFixedGroup t F θ⁆).map (baseChangeGL τ.toRingHom) ≤
      ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ := by
  rw [Subgroup.map_commutator]
  have h : (twistedFixedGroup t F θ).map (baseChangeGL τ.toRingHom) ≤
      twistedFixedGroup t K σ := by
    rintro _ ⟨g, hg, rfl⟩
    exact baseChangeGL_mem_twistedFixedGroup_of_comp τ hτ t hg
  exact Subgroup.commutator_mono h h

@[expose] noncomputable def derivedEquiv (hτ : τ.toRingHom.comp θ = σ.comp τ.toRingHom)
    (hτ' : τ.symm.toRingHom.comp σ = θ.comp τ.symm.toRingHom) (t : TwistTag) :
    ↥⁅twistedFixedGroup t F θ, twistedFixedGroup t F θ⁆ ≃*
      ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ where
  toFun g := ⟨baseChangeGL τ.toRingHom g, map_derived_le τ hτ t ⟨g, g.2, rfl⟩⟩
  invFun g := ⟨baseChangeGL τ.symm.toRingHom g, map_derived_le τ.symm hτ' t ⟨g, g.2, rfl⟩⟩
  left_inv g := Subtype.ext (by
    show baseChangeGL τ.symm.toRingHom (baseChangeGL τ.toRingHom (g : ModGL t.tag F)) = g
    rw [baseChangeGL_baseChangeGL, RingEquiv.symm_toRingHom_comp_toRingHom, baseChangeGL_id])
  right_inv g := Subtype.ext (by
    show baseChangeGL τ.toRingHom (baseChangeGL τ.symm.toRingHom (g : ModGL t.tag K)) = g
    rw [baseChangeGL_baseChangeGL, RingEquiv.toRingHom_comp_symm_toRingHom, baseChangeGL_id])
  map_mul' g h := Subtype.ext (map_mul (baseChangeGL τ.toRingHom) (g : ModGL t.tag F) h)

theorem coe_derivedEquiv (hτ : τ.toRingHom.comp θ = σ.comp τ.toRingHom)
    (hτ' : τ.symm.toRingHom.comp σ = θ.comp τ.symm.toRingHom) (t : TwistTag)
    (g : ↥⁅twistedFixedGroup t F θ, twistedFixedGroup t F θ⁆) :
    ((derivedEquiv τ hτ hτ' t g : ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆) :
      ModGL t.tag K) = baseChangeGL τ.toRingHom g :=
  rfl

end BaseChange

section Compat

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

@[expose] def IsCompat (σ : K →+* K) (b : Fin t.tag.rank → Kˣ) : Prop :=
  ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)

theorem isCompat_one : IsCompat (t := t) σ 1 := fun i => by simp

theorem IsCompat.mul {a b : Fin t.tag.rank → Kˣ} (ha : IsCompat σ a) (hb : IsCompat σ b) :
    IsCompat σ (a * b) := fun i => by
  rw [Pi.mul_apply, Pi.mul_apply, ha i, hb i, map_mul]

theorem IsCompat.inv {a : Fin t.tag.rank → Kˣ} (ha : IsCompat σ a) : IsCompat σ a⁻¹ := fun i => by
  rw [Pi.inv_apply, Pi.inv_apply, ha i, map_inv]

theorem isCompat_symm {F : Type} [Field F] (τ : F ≃+* K) {θ : F →+* F}
    (hτ' : τ.symm.toRingHom.comp σ = θ.comp τ.symm.toRingHom) {a : Fin t.tag.rank → Kˣ}
    (ha : IsCompat σ a) :
    IsCompat θ fun i => Units.map τ.symm.toRingHom.toMonoidHom (a i) := fun i => by
  apply Units.ext
  have h := congrArg (fun φ : K →+* F => φ (a i : K)) hτ'
  simp only [RingHom.comp_apply] at h
  beta_reduce
  rw [ha i]
  simp only [Units.coe_map]
  exact h


theorem rootDiagUnit_mem_normalizer_derived {b : Fin t.tag.rank → Kˣ} (hb : IsCompat σ b) :
    rootDiagUnit t.tag b ∈ Subgroup.normalizer
      ((⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ : Subgroup (ModGL t.tag K)) :
        Set (ModGL t.tag K)) := by
  have hmap := map_conj_eq_of_mem_normalizer
    (rootDiagUnit_mem_normalizer_twistedFixedGroup (t := t) (σ := σ) hb)
  have hmap' : (⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆).map
      (MulAut.conj (rootDiagUnit t.tag b)).toMonoidHom =
        ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ := by
    rw [Subgroup.map_commutator, hmap]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← hmap']
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← hmap'] at hg
    obtain ⟨g', hg', hgg'⟩ := hg
    have e : g' = g := by
      have h1 : rootDiagUnit t.tag b * g' * (rootDiagUnit t.tag b)⁻¹ =
          rootDiagUnit t.tag b * g * (rootDiagUnit t.tag b)⁻¹ := hgg'
      simpa using h1
    rwa [← e]

theorem conj_rootDiag_mem_derived {b : Fin t.tag.rank → Kˣ} (hb : IsCompat σ b)
    {g : ModGL t.tag K} (hg : g ∈ ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆) :
    rootDiagUnit t.tag b * g * (rootDiagUnit t.tag b)⁻¹ ∈
      ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ :=
  ((Subgroup.mem_normalizer_iff.mp (rootDiagUnit_mem_normalizer_derived hb)) g).mp hg

variable (t K σ) in
@[expose] def diagTw : Subgroup (Subgroup.normalizer
    ((⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ : Subgroup (ModGL t.tag K)) :
        Set (ModGL t.tag K))) where
  carrier := {x | ∃ g ∈ ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆,
    ∃ b : Fin t.tag.rank → Kˣ, IsCompat σ b ∧ (x : ModGL t.tag K) = g * rootDiagUnit t.tag b}
  mul_mem' := by
    rintro x y ⟨g, hg, a, ha, hx⟩ ⟨g', hg', b, hb, hy⟩
    refine ⟨g * (rootDiagUnit t.tag a * g' * (rootDiagUnit t.tag a)⁻¹),
      mul_mem hg (conj_rootDiag_mem_derived ha hg'), a * b, ha.mul hb, ?_⟩
    rw [Subgroup.coe_mul, hx, hy, ← MpStdE6.rootDiagUnit_mul]
    group
  one_mem' := ⟨1, one_mem _, 1, isCompat_one, by rw [MpStdE6.rootDiagUnit_one, mul_one]; rfl⟩
  inv_mem' := by
    rintro x ⟨g, hg, a, ha, hx⟩
    refine ⟨(rootDiagUnit t.tag a)⁻¹ * g⁻¹ * rootDiagUnit t.tag a, ?_, a⁻¹, ha.inv, ?_⟩
    · have h := conj_rootDiag_mem_derived ha.inv (inv_mem hg)
      rwa [← MpStdE6.rootDiagUnit_inv, inv_inv] at h
    · rw [Subgroup.coe_inv, hx, ← MpStdE6.rootDiagUnit_inv]
      group

end Compat

end MpStdTwE6

end CFSG.StandardType

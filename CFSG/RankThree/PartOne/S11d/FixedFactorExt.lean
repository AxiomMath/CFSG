module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDet

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitary

section Ext

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {V₁ W : Submodule K V}

theorem exists_decomp_of_isCompl (hc : IsCompl V₁ W) (v : V) :
    ∃ v₁ ∈ V₁, ∃ w ∈ W, v₁ + w = v := by
  have h1 : v ∈ V₁ ⊔ W := by rw [hc.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  exact ⟨a, ha, b, hb, hab⟩

variable (hc : IsCompl V₁ W)

@[expose] noncomputable def extMap (g : V₁ →ₗ[K] V₁) : V →ₗ[K] V :=
  LinearMap.ofIsCompl hc (V₁.subtype ∘ₗ g) W.subtype

theorem extMap_of_mem_left (g : V₁ →ₗ[K] V₁) {v : V} (hv : v ∈ V₁) :
    extMap hc g v = (g ⟨v, hv⟩ : V) := by
  have := LinearMap.ofIsCompl_apply_left hc (φ := V₁.subtype ∘ₗ g) (ψ := W.subtype) ⟨v, hv⟩
  simpa [extMap] using this

theorem extMap_of_mem_right (g : V₁ →ₗ[K] V₁) {w : V} (hw : w ∈ W) : extMap hc g w = w := by
  have := LinearMap.ofIsCompl_apply_right hc (φ := V₁.subtype ∘ₗ g) (ψ := W.subtype) ⟨w, hw⟩
  simpa [extMap] using this

theorem extMap_apply (g : V₁ →ₗ[K] V₁) {v₁ w : V} (hv₁ : v₁ ∈ V₁) (hw : w ∈ W) :
    extMap hc g (v₁ + w) = (g ⟨v₁, hv₁⟩ : V) + w := by
  rw [map_add, extMap_of_mem_left hc g hv₁, extMap_of_mem_right hc g hw]

theorem extMap_mul (g g' : V₁ →ₗ[K] V₁) : extMap hc (g * g') = extMap hc g * extMap hc g' := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_decomp_of_isCompl hc v
  rw [Module.End.mul_apply, extMap_apply hc g' hv₁ hw, extMap_apply hc (g * g') hv₁ hw,
    extMap_apply hc g (g' ⟨v₁, hv₁⟩).2 hw]
  simp [Module.End.mul_apply]

theorem extMap_one : extMap hc (1 : V₁ →ₗ[K] V₁) = 1 := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_decomp_of_isCompl hc v
  rw [extMap_apply hc _ hv₁ hw]
  simp

@[expose] noncomputable def extEnd : Module.End K V₁ →* Module.End K V where
  toFun := extMap hc
  map_one' := extMap_one hc
  map_mul' := extMap_mul hc

theorem extEnd_injective : Function.Injective (extEnd hc) := by
  intro g g' hgg
  refine LinearMap.ext fun x => Subtype.ext ?_
  have h1 : extMap hc g (x : V) = extMap hc g' (x : V) := congrArg (fun f => f (x : V)) hgg
  rwa [extMap_of_mem_left hc g x.2, extMap_of_mem_left hc g' x.2] at h1

@[expose] noncomputable def extGL :
    LinearMap.GeneralLinearGroup K V₁ →* LinearMap.GeneralLinearGroup K V :=
  Units.map (extEnd hc)

theorem coe_extGL (g : LinearMap.GeneralLinearGroup K V₁) :
    ((extGL hc g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
      extMap hc (g : V₁ →ₗ[K] V₁) := rfl

theorem extGL_injective : Function.Injective (extGL hc) :=
  Units.map_injective (extEnd_injective hc)

theorem extGL_apply_left (g : LinearMap.GeneralLinearGroup K V₁) {v : V} (hv : v ∈ V₁) :
    (extGL hc g : V →ₗ[K] V) v = ((g : V₁ →ₗ[K] V₁) ⟨v, hv⟩ : V) :=
  extMap_of_mem_left hc _ hv

theorem extGL_apply_right (g : LinearMap.GeneralLinearGroup K V₁) {w : V} (hw : w ∈ W) :
    (extGL hc g : V →ₗ[K] V) w = w :=
  extMap_of_mem_right hc _ hw

section Form

variable {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem extMap_isom (hperp : ∀ v ∈ V₁, ∀ w ∈ W, B v w = 0)
    (hperp' : ∀ w ∈ W, ∀ v ∈ V₁, B w v = 0) {g : V₁ →ₗ[K] V₁}
    (hg : ∀ x y : V₁, B (g x : V) (g y : V) = B (x : V) (y : V)) (v w : V) :
    B (extMap hc g v) (extMap hc g w) = B v w := by
  obtain ⟨v₁, hv₁, a, ha, rfl⟩ := exists_decomp_of_isCompl hc v
  obtain ⟨w₁, hw₁, b, hb, rfl⟩ := exists_decomp_of_isCompl hc w
  rw [extMap_apply hc g hv₁ ha, extMap_apply hc g hw₁ hb]
  simp only [map_add, LinearMap.add_apply]
  rw [hperp _ (g ⟨v₁, hv₁⟩).2 b hb, hperp' a ha _ (g ⟨w₁, hw₁⟩).2, hperp v₁ hv₁ b hb,
    hperp' a ha w₁ hw₁]
  have := hg ⟨v₁, hv₁⟩ ⟨w₁, hw₁⟩
  rw [this]

end Form

variable [FiniteDimensional K V]

theorem det_extMap (g : V₁ →ₗ[K] V₁) : LinearMap.det (extMap hc g) = LinearMap.det g := by
  have hV : ∀ v ∈ V₁, extMap hc g v ∈ V₁ := fun v hv => by
    rw [extMap_of_mem_left hc g hv]; exact (g ⟨v, hv⟩).2
  have hW : ∀ w ∈ W, extMap hc g w ∈ W := fun w hw => by
    rw [extMap_of_mem_right hc g hw]; exact hw
  rw [det_eq_mul_det_of_isCompl hc _ hV hW]
  have h1 : (extMap hc g).restrict hV = g := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact extMap_of_mem_left hc g x.2
  have h2 : (extMap hc g).restrict hW = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact extMap_of_mem_right hc g x.2
  rw [h1, h2, LinearMap.det_id, mul_one]

section Herm

variable {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}

@[expose] noncomputable def Dfix (B : V →ₛₗ[σ] V →ₗ[K] K) (hc : IsCompl V₁ W) :
    Subgroup (LinearMap.GeneralLinearGroup K V) :=
  (sesqSpecialUnitaryGroup (B.domRestrict₁₂ V₁ V₁)).map (extGL hc)

omit [FiniteDimensional K V] in
theorem inv_apply_of_fix (γ : LinearMap.GeneralLinearGroup K V) {w : V}
    (hw : (γ : V →ₗ[K] V) w = w) :
    ((γ⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) w = w := by
  have h1 := congrArg (fun f : V →ₗ[K] V => f w) (Units.inv_mul γ)
  simp only [Module.End.mul_apply, Module.End.one_apply] at h1
  rw [hw] at h1
  exact h1

omit [FiniteDimensional K V] in
theorem apply_inv_apply' (γ : LinearMap.GeneralLinearGroup K V) (x : V) :
    (γ : V →ₗ[K] V) (((γ⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) = x := by
  have h1 := congrArg (fun f : V →ₗ[K] V => f x) (Units.mul_inv γ)
  simpa only [Module.End.mul_apply, Module.End.one_apply] using h1

omit [FiniteDimensional K V] in
theorem inv_apply_apply' (γ : LinearMap.GeneralLinearGroup K V) (x : V) :
    ((γ⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((γ : V →ₗ[K] V) x) = x := by
  have h1 := congrArg (fun f : V →ₗ[K] V => f x) (Units.inv_mul γ)
  simpa only [Module.End.mul_apply, Module.End.one_apply] using h1

theorem mem_Dfix_iff (hH : ∀ x y, B y x = σ (B x y))
    (hperp : ∀ v ∈ V₁, ∀ w ∈ W, B v w = 0) (hperp' : ∀ w ∈ W, ∀ v ∈ V₁, B w v = 0)
    (hsep : ∀ w ∈ W, (∀ w' ∈ W, B w w' = 0) → w = 0)
    (γ : LinearMap.GeneralLinearGroup K V) :
    γ ∈ Dfix B hc ↔ γ ∈ sesqSpecialUnitaryGroup B ∧ ∀ w ∈ W, (γ : V →ₗ[K] V) w = w := by
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    obtain ⟨hδU, hδdet⟩ := mem_sesqSpecialUnitaryGroup.mp hδ
    refine ⟨mem_sesqSpecialUnitaryGroup.mpr ⟨fun x y => ?_, ?_⟩, fun w hw => ?_⟩
    · exact extMap_isom hc hperp hperp' (fun a b => mem_sesqUnitaryGroup.mp hδU a b) x y
    · rw [coe_extGL, det_extMap hc]; exact hδdet
    · exact extGL_apply_right hc δ hw
  · rintro ⟨hγ, hfix⟩
    obtain ⟨hγU, hγdet⟩ := mem_sesqSpecialUnitaryGroup.mp hγ
    have hinv : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ sesqUnitaryGroup B →
        (∀ w ∈ W, (g : V →ₗ[K] V) w = w) → ∀ v ∈ V₁, (g : V →ₗ[K] V) v ∈ V₁ := by
      intro g hg hgw v hv
      obtain ⟨a, ha, w', hw', hdec⟩ := exists_decomp_of_isCompl hc ((g : V →ₗ[K] V) v)
      have hw'0 : w' = 0 := by
        apply hsep w' hw'
        intro w'' hw''
        have h1 : B w'' w' = 0 := by
          have h2 : w' = (g : V →ₗ[K] V) v - a := by rw [← hdec]; abel
          have h3 : B w'' ((g : V →ₗ[K] V) v) = 0 := by
            have := mem_sesqUnitaryGroup.mp hg w'' v
            rw [hgw w'' hw''] at this
            rw [this]
            exact hperp' w'' hw'' v hv
          rw [h2, map_sub, h3, hperp' w'' hw'' a ha, sub_zero]
        rw [hH w'' w', h1, map_zero]
      rw [← hdec, hw'0, add_zero]
      exact ha
    have hγV := hinv γ hγU hfix
    have hγ'V := hinv γ⁻¹ (inv_mem hγU) (fun w hw => inv_apply_of_fix γ (hfix w hw))
    have hγW : ∀ w ∈ W, (γ : V →ₗ[K] V) w ∈ W := fun w hw => by rw [hfix w hw]; exact hw
    let δ : LinearMap.GeneralLinearGroup K V₁ :=
      ⟨(γ : V →ₗ[K] V).restrict hγV, ((γ⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V).restrict
        hγ'V, LinearMap.ext fun x => Subtype.ext (apply_inv_apply' γ x),
        LinearMap.ext fun x => Subtype.ext (inv_apply_apply' γ x)⟩
    have hδU : δ ∈ sesqUnitaryGroup (B.domRestrict₁₂ V₁ V₁) := fun x y =>
      mem_sesqUnitaryGroup.mp hγU x y
    have hδdet : LinearMap.det (δ : V₁ →ₗ[K] V₁) = 1 := by
      have h1 := det_eq_mul_det_of_isCompl hc (γ : V →ₗ[K] V) hγV hγW
      have h2 : (γ : V →ₗ[K] V).restrict hγW = LinearMap.id :=
        LinearMap.ext fun x => Subtype.ext (hfix x x.2)
      rw [h2, LinearMap.det_id, mul_one] at h1
      rw [← hγdet, h1]
    refine ⟨δ, mem_sesqSpecialUnitaryGroup.mpr ⟨hδU, hδdet⟩, ?_⟩
    refine Units.ext (LinearMap.ext fun v => ?_)
    obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_decomp_of_isCompl hc v
    rw [coe_extGL, extMap_apply hc _ hv₁ hw, map_add, hfix w hw]
    rfl

end Herm

end Ext

end CFSG.RankThree.PartOne

module

public import CFSG.Quasithin.Background.G12FourBasic

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V']

@[expose] def fourConj (φ : V' ≃ₗ[ZMod 2] V) : GLV V ≃* GLV V' where
  toFun g := φ.trans (g.trans φ.symm)
  invFun g := φ.symm.trans (g.trans φ)
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g h := by ext x; simp

theorem fourConj_apply (φ : V' ≃ₗ[ZMod 2] V) (g : GLV V) (x : V') :
    fourConj φ g x = φ.symm (g (φ x)) := rfl

variable {B : LinearMap.BilinForm (ZMod 2) V} {B' : LinearMap.BilinForm (ZMod 2) V'}
  {φ : V' ≃ₗ[ZMod 2] V}

theorem g12f_isSymplectic_of_isometry (hφ : ∀ x y, B (φ x) (φ y) = B' x y) (hB : IsSymplectic B) :
    IsSymplectic B' := by
  refine ⟨fun x => by rw [← hφ]; exact hB.1 _, fun x hx => ?_⟩
  have : φ x = 0 := hB.2 _ fun z => by
    rw [← LinearEquiv.apply_symm_apply φ z, hφ]; exact hx _
  simpa using this

theorem fourConj_mem_spSub (hφ : ∀ x y, B (φ x) (φ y) = B' x y) {g : GLV V}
    (hg : g ∈ spSub B) : fourConj φ g ∈ spSub B' := by
  intro x y
  show B' (φ.symm (g (φ x))) (φ.symm (g (φ y))) = B' x y
  rw [← hφ, ← hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hg _ _

theorem fourConj_symm_mem_spSub (hφ : ∀ x y, B (φ x) (φ y) = B' x y) {g : GLV V'}
    (hg : g ∈ spSub B') : (fourConj φ).symm g ∈ spSub B := by
  intro x y
  show B (φ (g (φ.symm x))) (φ (g (φ.symm y))) = B x y
  rw [hφ, hg]
  have := hφ (φ.symm x) (φ.symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem fourConj_radE (hφ : ∀ x y, B (φ x) (φ y) = B' x y) (hB : IsSymplectic B) {w a : V}
    (hwa : B w a = 0) (c : ZMod 2) :
    fourConj φ (radE B w a c) = radE B' (φ.symm w) (φ.symm a) c := by
  have hB' := g12f_isSymplectic_of_isometry hφ hB
  have hwa' : B' (φ.symm w) (φ.symm a) = 0 := by
    rw [← hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]; exact hwa
  have e : ∀ x z, B (φ x) z = B' x (φ.symm z) := fun x z => by
    rw [← hφ, LinearEquiv.apply_symm_apply]
  refine LinearEquiv.ext fun x => ?_
  rw [fourConj_apply, radE_apply hB hwa, radE_apply hB' hwa', e, e]
  simp

@[expose] def fourConjSub (φ : V' ≃ₗ[ZMod 2] V) (Γ : Subgroup (GLV V)) : Subgroup (GLV V') :=
  Γ.map (fourConj φ).toMonoidHom

theorem mem_fourConjSub {Γ : Subgroup (GLV V)} {g : GLV V'} :
    g ∈ fourConjSub φ Γ ↔ (fourConj φ).symm g ∈ Γ := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa using hh
  · intro hg
    exact ⟨(fourConj φ).symm g, hg, by simp⟩

theorem fourConj_mem_fourConjSub {Γ : Subgroup (GLV V)} {g : GLV V} (hg : g ∈ Γ) :
    fourConj φ g ∈ fourConjSub φ Γ :=
  ⟨g, hg, rfl⟩

theorem fourConjSub_le_spSub (hφ : ∀ x y, B (φ x) (φ y) = B' x y) {Γ : Subgroup (GLV V)}
    (hΓ : Γ ≤ spSub B) : fourConjSub φ Γ ≤ spSub B' := by
  rintro _ ⟨g, hg, rfl⟩
  exact fourConj_mem_spSub hφ (hΓ hg)

theorem radE_mem_fourConjSub_iff (hφ : ∀ x y, B (φ x) (φ y) = B' x y) (hB : IsSymplectic B)
    {Γ : Subgroup (GLV V)} {w a : V'} (hwa : B' w a = 0) (c : ZMod 2) :
    radE B' w a c ∈ fourConjSub φ Γ ↔ radE B (φ w) (φ a) c ∈ Γ := by
  have hwa' : B (φ w) (φ a) = 0 := by rw [hφ]; exact hwa
  have h := fourConj_radE hφ hB hwa' c
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
  rw [← h, mem_fourConjSub, MulEquiv.symm_apply_apply]

theorem fourElliptic_fourConjSub_iff (hφ : ∀ x y, B (φ x) (φ y) = B' x y) (hB : IsSymplectic B)
    {Γ : Subgroup (GLV V)} {w : V'} :
    FourElliptic B' (fourConjSub φ Γ) w ↔ FourElliptic B Γ (φ w) := by
  constructor
  · intro h a hwa ha0 haw
    have hwa' : B' w (φ.symm a) = 0 := by
      rw [← hφ, LinearEquiv.apply_symm_apply]; exact hwa
    have := (radE_mem_fourConjSub_iff hφ hB hwa' 1).1 (h (φ.symm a) hwa'
      (fun h0 => ha0 (by simpa using h0)) (fun h1 => haw (by rw [← h1]; simp)))
    rwa [LinearEquiv.apply_symm_apply] at this
  · intro h a hwa ha0 haw
    refine (radE_mem_fourConjSub_iff hφ hB hwa 1).2 (h (φ a) (by rw [hφ]; exact hwa)
      (fun h0 => ha0 (by simpa using h0)) (fun h1 => haw (φ.injective h1)))

theorem nonempty_mulEquiv_of_fourConjSub {P : Type} [Group P] {Γ : Subgroup (GLV V)}
    (h : Nonempty (↥(fourConjSub φ Γ) ≃* P)) : Nonempty (↥Γ ≃* P) :=
  h.map fun e => ((fourConj φ).subgroupMap Γ).trans e

theorem exists_isL24_of_fourConjSub {Γ : Subgroup (GLV V)} {A' : Subgroup (GLV V')}
    (hA' : A' ≤ fourConjSub φ Γ) (hL : IsL24ModuleFor A') :
    ∃ A : Subgroup (GLV V), A ≤ Γ ∧ IsL24ModuleFor A := by
  obtain ⟨⟨eA⟩, ω, hω, hcomm⟩ := hL
  refine ⟨A'.map (fourConj φ).symm.toMonoidHom, ?_, ⟨?_⟩, (fourConj φ).symm ω, fun x => ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_fourConjSub.1 (hA' ha)
  · exact (((fourConj φ).symm.subgroupMap A').symm).trans eA
  · have h := hω (φ.symm x)
    show φ (ω (φ.symm (φ (ω (φ.symm x))))) + φ (ω (φ.symm x)) + x = 0
    calc φ (ω (φ.symm (φ (ω (φ.symm x))))) + φ (ω (φ.symm x)) + x
        = φ (ω (ω (φ.symm x)) + ω (φ.symm x) + φ.symm x) := by
          rw [LinearEquiv.symm_apply_apply, map_add, map_add, LinearEquiv.apply_symm_apply]
      _ = 0 := by rw [h, map_zero]
  · rintro _ ⟨a, ha, rfl⟩
    show (fourConj φ).symm a * (fourConj φ).symm ω = (fourConj φ).symm ω * (fourConj φ).symm a
    rw [← map_mul, ← map_mul, hcomm a ha]

variable [Finite V] [Finite V']

theorem isStarVec_fourConj (hφ : ∀ x y, B (φ x) (φ y) = B' x y) (hB : IsSymplectic B)
    {Γ : Subgroup (GLV V)} (hΓ : Γ ≤ spSub B) {w : V'} (hw : IsStarVec B Γ (φ w)) :
    IsStarVec B' (fourConjSub φ Γ) w := by
  have hB' := g12f_isSymplectic_of_isometry hφ hB
  rw [isStarVec_iff_rad hB hΓ] at hw
  rw [isStarVec_iff_rad hB' (fourConjSub_le_spSub hφ hΓ)]
  refine ⟨fun h0 => hw.1 (by rw [h0, map_zero]), fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := hw.2 (φ a) (by rw [hφ]; exact ha)
  exact ⟨c, (radE_mem_fourConjSub_iff hφ hB ha c).2 hc⟩

end NoInst

end CFSG.Quasithin.G11

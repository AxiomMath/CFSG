module

public import CFSG.Quasithin.Background.E11Setup

public section

namespace CFSG.Quasithin

namespace G11

namespace E11

open scoped LinearAlgebra.Projectivization

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

theorem cent_comm {c : GLV V} (hc : c ∈ Subgroup.centralizer (H : Set (GLV V)))
    {a : Module.End (ZMod 2) V} (ha : a ∈ hAlg H) :
    (c : Module.End (ZMod 2) V) * a = a * (c : Module.End (ZMod 2) V) := by
  have h1 : (c : Module.End (ZMod 2) V) ∈ Subalgebra.centralizer (ZMod 2) (hGens H) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hc h hh
    ext v
    exact congrArg (fun x : GLV V => x v) this
  have h2 := Algebra.adjoin_le_centralizer_centralizer (ZMod 2) (hGens H) ha
  exact (Subalgebra.mem_centralizer_iff (ZMod 2)).1 h2 _ h1

@[expose] def centEnd (c : Subgroup.centralizer (H : Set (GLV V))) : Module.End (HRing H) V where
  toFun v := (c : GLV V) v
  map_add' := map_add _
  map_smul' a v := by
    have := cent_comm c.2 a.val_mem
    exact congrArg (fun f : Module.End (ZMod 2) V => f v) this

@[simp] theorem centEnd_apply (c : Subgroup.centralizer (H : Set (GLV V))) (v : V) :
    centEnd c v = (c : GLV V) v := rfl

theorem centEnd_mul (c d : Subgroup.centralizer (H : Set (GLV V))) :
    centEnd (c * d) = centEnd c * centEnd d := rfl

theorem centEnd_one : centEnd (1 : Subgroup.centralizer (H : Set (GLV V))) = 1 := rfl

theorem centEnd_injective :
    Function.Injective (centEnd (H := H)) := fun c d h => by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  exact congrArg (fun f : Module.End (HRing H) V => f v) h

section Theta

variable [Finite V] {I' : Submodule (HRing H) V} [IsSimpleModule (HRing H) I']

@[expose] def centMonoidHom : Subgroup.centralizer (H : Set (GLV V)) →* Module.End (HRing H) V where
  toFun := centEnd
  map_one' := centEnd_one
  map_mul' := centEnd_mul

@[expose] noncomputable def thetaHom : Subgroup.centralizer (H : Set (GLV V)) →*
    ((I' →ₗ[HRing H] V) ≃ₗ[Module.End (HRing H) I'] (I' →ₗ[HRing H] V)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).toMonoidHom.comp
    ((postcomp (R := HRing H) (I := I') (V := V)).toMonoidHom.comp centMonoidHom).toHomUnits

variable {n : ℕ} (e : V ≃ₗ[HRing H] (Fin n → ↥I'))

include e in
theorem thetaHom_injective : Function.Injective (thetaHom (H := H) (I' := I')) := by
  intro c d h
  refine centEnd_injective (postcomp_injective e (LinearMap.ext fun φ => LinearMap.ext fun i => ?_))
  have := congrArg (fun σ => σ φ i) h
  exact this

include e in
theorem thetaHom_surjective : Function.Surjective (thetaHom (H := H) (I' := I')) := by
  intro σ
  obtain ⟨g₁, hg₁⟩ := (postcomp_bijective e).2 (σ : Module.End (Module.End (HRing H) I')
    (I' →ₗ[HRing H] V))
  obtain ⟨g₂, hg₂⟩ := (postcomp_bijective e).2 (σ.symm : Module.End (Module.End (HRing H) I')
    (I' →ₗ[HRing H] V))
  have h12 : g₁ * g₂ = 1 := (postcomp_bijective e).1 (by
    rw [RingHom.map_mul, RingHom.map_one, hg₁, hg₂]
    exact LinearMap.ext fun φ => σ.apply_symm_apply φ)
  have h21 : g₂ * g₁ = 1 := (postcomp_bijective e).1 (by
    rw [RingHom.map_mul, RingHom.map_one, hg₁, hg₂]
    exact LinearMap.ext fun φ => σ.symm_apply_apply φ)
  let c : GLV V := LinearEquiv.ofLinearMap (g₁.restrictScalars (ZMod 2))
    (g₂.restrictScalars (ZMod 2))
    (LinearMap.ext fun v => congrArg (fun f : Module.End (HRing H) V => f v) h12)
    (LinearMap.ext fun v => congrArg (fun f : Module.End (HRing H) V => f v) h21)
  have hc : c ∈ Subgroup.centralizer (H : Set (GLV V)) := by
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    refine LinearEquiv.ext fun v => ?_
    have := g₁.map_smul (genElem H ⟨h, hh⟩) v
    exact this.symm
  refine ⟨⟨c, hc⟩, LinearEquiv.ext fun φ => LinearMap.ext fun i => ?_⟩
  have := congrArg (fun f : Module.End (Module.End (HRing H) I') (I' →ₗ[HRing H] V) => f φ i) hg₁
  exact this

@[expose] noncomputable def thetaEquiv : Subgroup.centralizer (H : Set (GLV V)) ≃*
    ((I' →ₗ[HRing H] V) ≃ₗ[Module.End (HRing H) I'] (I' →ₗ[HRing H] V)) :=
  MulEquiv.ofBijective thetaHom ⟨thetaHom_injective e, thetaHom_surjective e⟩

theorem pointSub_smul (c : Subgroup.centralizer (H : Set (GLV V)))
    (p : ℙ (Module.End (HRing H) I') (I' →ₗ[HRing H] V)) :
    pointSub I' (thetaEquiv e c • p) = conjSub (c : GLV V) (pointSub I' p) := by
  induction p using Projectivization.ind with
  | h φ hφ =>
    rw [Projectivization.smul_mk]
    ext v
    rw [mem_conjSub]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have : (c : GLV V) (φ i) = v := hi
      rw [← this]
      simp
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      show (c : GLV V) (φ i) = v
      rw [hi]
      simp

end Theta

end E11

end G11

end CFSG.Quasithin

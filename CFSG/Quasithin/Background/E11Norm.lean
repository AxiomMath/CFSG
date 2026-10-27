module

public import CFSG.Quasithin.Background.E11Cent

public section

namespace CFSG.Quasithin

namespace G11

namespace E11

open scoped LinearAlgebra.Projectivization

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

section Conj

variable {g : GLV V}

private theorem coe_mul_end (a b : GLV V) :
    ((a * b : GLV V) : Module.End (ZMod 2) V) =
      (a : Module.End (ZMod 2) V) * (b : Module.End (ZMod 2) V) := rfl

private theorem coe_inv_mul_end (a : GLV V) :
    (a : Module.End (ZMod 2) V) * ((a⁻¹ : GLV V) : Module.End (ZMod 2) V) = 1 := by
  rw [← coe_mul_end, mul_inv_cancel]
  rfl

private theorem coe_inv_mul_end' (a : GLV V) :
    ((a⁻¹ : GLV V) : Module.End (ZMod 2) V) * (a : Module.End (ZMod 2) V) = 1 := by
  rw [← coe_mul_end, inv_mul_cancel]
  rfl

theorem conj_mem_hAlg (hg : g ∈ Subgroup.normalizer (H : Set (GLV V)))
    {a : Module.End (ZMod 2) V} (ha : a ∈ hAlg H) :
    (g : Module.End (ZMod 2) V) * a * ((g⁻¹ : GLV V) : Module.End (ZMod 2) V) ∈ hAlg H := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    have : g * h * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hg h).1 hh
    have h2 := hAlg_mem_of_mem this
    rwa [coe_mul_end, coe_mul_end] at h2
  | algebraMap c =>
    have : (g : Module.End (ZMod 2) V) * algebraMap (ZMod 2) (Module.End (ZMod 2) V) c *
        ((g⁻¹ : GLV V) : Module.End (ZMod 2) V) =
          algebraMap (ZMod 2) (Module.End (ZMod 2) V) c := by
      rw [← Algebra.commutes, mul_assoc, coe_inv_mul_end, mul_one]
    rw [this]
    exact Subalgebra.algebraMap_mem _ c
  | add x y _ _ hx hy =>
    rw [mul_add, add_mul]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    have : (g : Module.End (ZMod 2) V) * (x * y) * ((g⁻¹ : GLV V) : Module.End (ZMod 2) V) =
        ((g : Module.End (ZMod 2) V) * x * ((g⁻¹ : GLV V) : Module.End (ZMod 2) V)) *
          ((g : Module.End (ZMod 2) V) * y * ((g⁻¹ : GLV V) : Module.End (ZMod 2) V)) := by
      simp only [mul_assoc]
      rw [← mul_assoc ((g⁻¹ : GLV V) : Module.End (ZMod 2) V), coe_inv_mul_end', one_mul]
    rw [this]
    exact mul_mem hx hy

@[expose] def conjH (hg : g ∈ Subgroup.normalizer (H : Set (GLV V))) (a : HRing H) : HRing H :=
  (⟨(g : Module.End (ZMod 2) V) * a.val * ((g⁻¹ : GLV V) : Module.End (ZMod 2) V),
    conj_mem_hAlg hg a.val_mem⟩ : ↥(hAlg H))

theorem smul_conj (hg : g ∈ Subgroup.normalizer (H : Set (GLV V))) (a : HRing H) (v : V) :
    g (a • v) = conjH hg a • g v := by
  show g (a.val v) = ((g : Module.End (ZMod 2) V) * a.val *
    ((g⁻¹ : GLV V) : Module.End (ZMod 2) V)) (g v)
  simp

theorem conjH_conjH (hg : g ∈ Subgroup.normalizer (H : Set (GLV V)))
    (hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set (GLV V))) (a : HRing H) :
    conjH hg (conjH hg' a) = a := by
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  show g (g⁻¹ (a.val (g (g⁻¹ v)))) = a.val v
  simp

theorem conjH_conjH' (hg : g ∈ Subgroup.normalizer (H : Set (GLV V)))
    (hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set (GLV V))) (a : HRing H) :
    conjH hg' (conjH hg a) = a := by
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  show g⁻¹ (g (a.val (g⁻¹ ((g⁻¹)⁻¹ v)))) = a.val v
  simp

end Conj

section Twist

variable {g : GLV V}

structure Twist (hg : g ∈ Subgroup.normalizer (H : Set (GLV V))) (I' : Submodule (HRing H) V) where
  ρ : I' ≃+ I'
  map_smul : ∀ (a : HRing H) (i : I'), ρ (a • i) = conjH (Subgroup.inv_mem _ hg) a • ρ i

variable {hg : g ∈ Subgroup.normalizer (H : Set (GLV V))} {I' : Submodule (HRing H) V}

theorem Twist.map_smul_symm (T : Twist hg I') (b : HRing H) (j : I') :
    T.ρ.symm (b • j) = conjH hg b • T.ρ.symm j := by
  apply T.ρ.injective
  rw [AddEquiv.apply_symm_apply, T.map_smul, AddEquiv.apply_symm_apply,
    conjH_conjH' hg (Subgroup.inv_mem _ hg)]

section Exists

variable [IsSimpleModule (HRing H) I']

theorem nonempty_twist (hiso : IsIsotypicOfType (HRing H) V I')
    (hg : g ∈ Subgroup.normalizer (H : Set (GLV V))) : Nonempty (Twist hg I') := by
  have hI : IsIrr H (I'.restrictScalars (ZMod 2)) :=
    isIrr_iff_isAtom.2 (isSimpleModule_iff_isAtom.1 ‹_›)
  have hN : ∀ γ ∈ Subgroup.normalizer (H : Set (GLV V)), ∀ n ∈ H, γ * n * γ⁻¹ ∈ H :=
    fun γ hγ n hn => (Subgroup.mem_normalizer_iff.1 hγ n).1 hn
  have hJ : IsIrr H (conjSub g (I'.restrictScalars (ZMod 2))) :=
    IsIrr.conj_of_normal (Γ := Subgroup.normalizer (H : Set (GLV V))) hN hI hg
  set J : Submodule (HRing H) V := ofInvariant _ hJ.1 with hJdef
  have hJa : IsAtom J := isIrr_iff_isAtom.1 hJ
  have : IsSimpleModule (HRing H) J := isSimpleModule_iff_isAtom.2 hJa
  obtain ⟨β⟩ := hiso J
  have hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set (GLV V)) := Subgroup.inv_mem _ hg
  have hmem : ∀ x : J, g.symm (x : V) ∈ I' := fun x => mem_conjSub.1 x.2
  have hmem' : ∀ j : I', g (j : V) ∈ J := fun j => apply_mem_conjSub j.2
  let f : I' → I' := fun i => ⟨g.symm ((β.symm i : J) : V), hmem _⟩
  let f' : I' → I' := fun j => β ⟨g (j : V), hmem' j⟩
  have hli : ∀ i : I', f' (f i) = i := by
    intro i
    have : (⟨g ((f i : I') : V), hmem' (f i)⟩ : J) = β.symm i :=
      Subtype.ext (by show g (g.symm ((β.symm i : J) : V)) = _; simp)
    show β ⟨g ((f i : I') : V), hmem' (f i)⟩ = i
    rw [this, LinearEquiv.apply_symm_apply]
  have hri : ∀ j : I', f (f' j) = j := by
    intro j
    refine Subtype.ext ?_
    show g.symm ((β.symm (β ⟨g (j : V), hmem' j⟩) : J) : V) = j
    rw [LinearEquiv.symm_apply_apply]
    simp
  let ρ : I' ≃+ I' :=
    { toFun := f
      invFun := f'
      left_inv := hli
      right_inv := hri
      map_add' := fun i j => by
        refine Subtype.ext ?_
        show g.symm ((β.symm (i + j) : J) : V) =
          g.symm ((β.symm i : J) : V) + g.symm ((β.symm j : J) : V)
        rw [map_add, Submodule.coe_add, map_add] }
  refine ⟨⟨ρ, fun a i => ?_⟩⟩
  refine Subtype.ext ?_
  show g.symm ((β.symm (a • i) : J) : V) =
    (conjH hg' a • (⟨g.symm ((β.symm i : J) : V), hmem _⟩ : I') : V)
  rw [map_smul]
  exact smul_conj hg' a _

end Exists

section Sigma0

variable (T : Twist hg I')

@[expose] def sigmaMap (φ : I' →ₗ[HRing H] V) : I' →ₗ[HRing H] V where
  toFun i := g (φ (T.ρ i))
  map_add' i j := by simp
  map_smul' a i := by
    simp only [RingHom.id_apply]
    rw [T.map_smul, φ.map_smul, smul_conj hg, conjH_conjH hg (Subgroup.inv_mem _ hg)]

@[expose] noncomputable def tauEnd (f : Module.End (HRing H) I') : Module.End (HRing H) I' where
  toFun i := T.ρ.symm (f (T.ρ i))
  map_add' i j := by simp
  map_smul' a i := by
    simp only [RingHom.id_apply]
    rw [T.map_smul, f.map_smul, T.map_smul_symm, conjH_conjH hg (Subgroup.inv_mem _ hg)]

@[expose] noncomputable def tauHom : Module.End (HRing H) I' →+* Module.End (HRing H) I' where
  toFun := tauEnd T
  map_one' := by
    ext i
    simp [tauEnd]
  map_mul' f f' := by
    ext i
    simp [tauEnd]
  map_zero' := by
    ext i
    simp [tauEnd]
  map_add' f f' := by
    ext i
    simp [tauEnd]

end Sigma0

section Sigma

variable [Finite V] [IsSimpleModule (HRing H) I'] (T : Twist hg I')

theorem tauHom_bijective : Function.Bijective (tauHom T) := by
  have : Finite (Module.End (HRing H) I') := FunLike.finite _
  exact Finite.injective_iff_bijective.1 (tauHom T).injective

@[expose] noncomputable def tauEquiv : Module.End (HRing H) I' ≃+* Module.End (HRing H) I' :=
  RingEquiv.ofBijective (tauHom T) (tauHom_bijective T)

@[expose] noncomputable def sigmaLin :
    (I' →ₗ[HRing H] V) →ₛₗ[(tauHom T : Module.End (HRing H) I' →+* Module.End (HRing H) I')]
      (I' →ₗ[HRing H] V) where
  toFun := sigmaMap T
  map_add' φ ψ := by
    ext i
    simp [sigmaMap]
  map_smul' f φ := by
    ext i
    show g (φ (f (T.ρ i))) = g (φ (T.ρ (T.ρ.symm (f (T.ρ i)))))
    simp

theorem sigmaLin_apply (φ : I' →ₗ[HRing H] V) (i : I') : sigmaLin T φ i = g (φ (T.ρ i)) := rfl

theorem sigmaLin_injective : Function.Injective (sigmaLin T) := by
  intro φ ψ h
  ext i
  have := congrArg (fun χ : I' →ₗ[HRing H] V => g (χ (T.ρ.symm i))) h
  simpa [sigmaLin_apply] using this

theorem sigmaLin_bijective : Function.Bijective (sigmaLin T) := by
  have : Finite (I' →ₗ[HRing H] V) := finite_hom
  exact Finite.injective_iff_bijective.1 (sigmaLin_injective T)

theorem pointSub_map_sigma (p : ℙ (Module.End (HRing H) I') (I' →ₗ[HRing H] V)) :
    pointSub I' (Projectivization.map (sigmaLin T) (sigmaLin_injective T) p) =
      conjSub g (pointSub I' p) := by
  induction p using Projectivization.ind with
  | h φ hφ =>
    rw [Projectivization.map_mk]
    ext v
    rw [mem_conjSub]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨T.ρ i, ?_⟩
      have : g (φ (T.ρ i)) = v := hi
      rw [← this]
      simp
    · rintro ⟨j, hj⟩
      refine ⟨T.ρ.symm j, ?_⟩
      show g (φ (T.ρ (T.ρ.symm j))) = v
      rw [AddEquiv.apply_symm_apply]
      have : φ j = g.symm v := hj
      rw [this]
      simp

end Sigma

end Twist

end E11

end G11

end CFSG.Quasithin

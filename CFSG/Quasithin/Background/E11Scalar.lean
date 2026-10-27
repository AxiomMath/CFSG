module

public import CFSG.Quasithin.Background.E11Cent

public section

namespace CFSG.Quasithin

namespace G11

namespace E11

open scoped LinearAlgebra.Projectivization

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

section Scalar

variable [Finite V] {I' : Submodule (HRing H) V} [IsSimpleModule (HRing H) I'] {n : ℕ}
  (e : V ≃ₗ[HRing H] (Fin n → ↥I'))

@[expose] noncomputable def postcompEquiv : Module.End (HRing H) V ≃+*
    Module.End (Module.End (HRing H) I') (I' →ₗ[HRing H] V) :=
  RingEquiv.ofBijective (postcomp (R := HRing H) (I := I') (V := V)) (postcomp_bijective e)

@[expose] noncomputable def scalarEnd (f : Module.End (HRing H) I') :
    Module.End (Module.End (HRing H) I') (I' →ₗ[HRing H] V) where
  toFun φ := f • φ
  map_add' := smul_add f
  map_smul' c φ := by
    show f • c • φ = c • f • φ
    rw [← mul_smul, ← mul_smul, mul_comm]

theorem scalarEnd_one :
    scalarEnd (1 : Module.End (HRing H) I') =
      (1 : Module.End (Module.End (HRing H) I') (I' →ₗ[HRing H] V)) :=
  LinearMap.ext fun φ => one_smul _ φ

theorem scalarEnd_mul (f f' : Module.End (HRing H) I') :
    scalarEnd (f * f') = (scalarEnd f * scalarEnd f' :
      Module.End (Module.End (HRing H) I') (I' →ₗ[HRing H] V)) :=
  LinearMap.ext fun φ => mul_smul f f' φ

theorem scalarEnd_zero :
    scalarEnd (0 : Module.End (HRing H) I') =
      (0 : Module.End (Module.End (HRing H) I') (I' →ₗ[HRing H] V)) :=
  LinearMap.ext fun φ => zero_smul _ φ

theorem scalarEnd_add (f f' : Module.End (HRing H) I') :
    scalarEnd (f + f') = (scalarEnd f + scalarEnd f' :
      Module.End (Module.End (HRing H) I') (I' →ₗ[HRing H] V)) :=
  LinearMap.ext fun φ => add_smul f f' φ

@[expose] noncomputable def kappaA : Module.End (HRing H) I' →+* Module.End (HRing H) V where
  toFun f := (postcompEquiv e).symm (scalarEnd f)
  map_one' := by rw [scalarEnd_one, map_one]
  map_mul' f f' := by rw [scalarEnd_mul, map_mul]
  map_zero' := by rw [scalarEnd_zero, map_zero]
  map_add' f f' := by rw [scalarEnd_add, map_add]

theorem postcomp_kappaA (f : Module.End (HRing H) I') :
    postcomp (kappaA e f) = scalarEnd f :=
  (postcompEquiv e).apply_symm_apply (scalarEnd f)

theorem kappaA_comp (f : Module.End (HRing H) I') (φ : I' →ₗ[HRing H] V) (i : I') :
    kappaA e f (φ i) = φ (f i) := by
  have h := congrArg (fun T : Module.End (Module.End (HRing H) I') (I' →ₗ[HRing H] V) => T φ i)
    (postcomp_kappaA e f)
  exact h

omit [Finite V] in
theorem two_eq_zero_end (I'' : Type*) [AddCommGroup I''] [Module (ZMod 2) I'']
    [Module (HRing H) I''] : (2 : Module.End (HRing H) I'') = 0 := by
  have h2 : ∀ x : I'', x + x = 0 := fun x => by
    rw [← two_nsmul]
    exact ZModModule.char_nsmul_eq_zero 2 x
  rw [← one_add_one_eq_two]
  ext x
  simp [h2]

instance instCharPEnd : CharP (Module.End (HRing H) I') 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (two_eq_zero_end I')

@[expose] noncomputable def kappaRing : Module.End (HRing H) I' →+* Module.End (ZMod 2) V where
  toFun f := (kappaA e f).restrictScalars (ZMod 2)
  map_one' := by
    ext v
    show kappaA e 1 v = v
    rw [map_one]
    rfl
  map_mul' f f' := by
    ext v
    show kappaA e (f * f') v = kappaA e f (kappaA e f' v)
    rw [map_mul]
    rfl
  map_zero' := by
    ext v
    show kappaA e 0 v = 0
    rw [map_zero]
    rfl
  map_add' f f' := by
    ext v
    show kappaA e (f + f') v = kappaA e f v + kappaA e f' v
    rw [map_add]
    rfl

@[expose] noncomputable def kappa :
    Module.End (HRing H) I' →ₐ[ZMod 2] Module.End (ZMod 2) V where
  toRingHom := kappaRing e
  commutes' c := by
    have := RingHom.ext_zmod ((kappaRing e).comp (algebraMap (ZMod 2) (Module.End (HRing H) I')))
      (algebraMap (ZMod 2) (Module.End (ZMod 2) V))
    exact congrArg (fun r => r c) this

theorem kappa_comm (f : Module.End (HRing H) I') (h : GLV V) (hh : h ∈ H) :
    kappa e f * (h : Module.End (ZMod 2) V) = (h : Module.End (ZMod 2) V) * kappa e f :=
  LinearMap.ext fun v => (kappaA e f).map_smul (genElem H ⟨h, hh⟩) v

theorem kappa_apply_mem (f : Module.End (HRing H) I') (i : I') :
    kappa e f (i : V) = ((f i : I') : V) :=
  kappaA_comp e f I'.subtype i

theorem kappa_stable (hfix : fixedSpace H = ⊥) (hiso : IsIsotypicOfType (HRing H) V I')
    (f : Module.End (HRing H) I') {J : Submodule (ZMod 2) V} (hJ : IrrPlus H J) :
    ∀ v ∈ J, kappa e f v ∈ J := by
  obtain ⟨p, rfl⟩ := pointSub_surjective hfix I' hiso hJ
  induction p using Projectivization.ind with
  | h φ hφ =>
    rintro v ⟨i, rfl⟩
    exact ⟨f i, (kappaA_comp e f φ i).symm⟩

theorem exists_cent_kappa {f : Module.End (HRing H) I'} (hf : f ≠ 0) :
    ∃ c : Subgroup.centralizer (H : Set (GLV V)), centEnd c = kappaA e f := by
  let σf : (I' →ₗ[HRing H] V) ≃ₗ[Module.End (HRing H) I'] (I' →ₗ[HRing H] V) :=
    LinearEquiv.smulOfNeZero _ _ f hf
  obtain ⟨c, hc⟩ := (thetaEquiv e).surjective σf
  refine ⟨c, postcomp_injective e (LinearMap.ext fun φ => LinearMap.ext fun i => ?_)⟩
  have h1 : thetaEquiv e c φ i = σf φ i := congrArg (fun T => T φ i) hc
  show (c : GLV V) (φ i) = kappaA e f (φ i)
  rw [kappaA_comp]
  exact h1

section Conj

variable {g : GLV V}

omit [Finite V] [IsSimpleModule (HRing H) I'] in
theorem conj_mem_cent (hg : g ∈ Subgroup.normalizer (H : Set (GLV V)))
    (c : Subgroup.centralizer (H : Set (GLV V))) :
    g * (c : GLV V) * g⁻¹ ∈ Subgroup.centralizer (H : Set (GLV V)) := by
  refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
  have hh' : g⁻¹ * h * g ∈ H := by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) h).1 hh
  have hc := Subgroup.mem_centralizer_iff.1 c.2 _ hh'
  calc h * (g * (c : GLV V) * g⁻¹) = g * ((g⁻¹ * h * g) * (c : GLV V)) * g⁻¹ := by group
    _ = g * ((c : GLV V) * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
    _ = g * (c : GLV V) * g⁻¹ * h := by group

theorem kappa_conj (hg : g ∈ Subgroup.normalizer (H : Set (GLV V)))
    (τ : Module.End (HRing H) I' ≃+* Module.End (HRing H) I')
    (σ : (I' →ₗ[HRing H] V) →ₛₗ[(τ : Module.End (HRing H) I' →+* Module.End (HRing H) I')]
      (I' →ₗ[HRing H] V))
    (hσ : Function.Bijective σ)
    (hcompat : ∀ c c' : Subgroup.centralizer (H : Set (GLV V)),
      (c' : GLV V) * g = g * c → ∀ u, thetaEquiv e c' (σ u) = σ (thetaEquiv e c u))
    (f : Module.End (HRing H) I') :
    (g : Module.End (ZMod 2) V) * kappa e f = kappa e (τ f) * (g : Module.End (ZMod 2) V) := by
  by_cases hf : f = 0
  · subst hf
    simp
  obtain ⟨c, hc⟩ := exists_cent_kappa e hf
  let c' : Subgroup.centralizer (H : Set (GLV V)) := ⟨g * (c : GLV V) * g⁻¹, conj_mem_cent hg c⟩
  have hcg : (c' : GLV V) * g = g * (c : GLV V) := by
    show g * (c : GLV V) * g⁻¹ * g = g * (c : GLV V)
    group
  have hcv : ∀ v, (c : GLV V) v = kappaA e f v := fun v =>
    congrArg (fun T : Module.End (HRing H) V => T v) hc
  have hthc : ∀ u, thetaEquiv e c u = f • u := by
    intro u
    refine LinearMap.ext fun i => ?_
    show (c : GLV V) (u i) = u (f i)
    rw [hcv, kappaA_comp]
  have hthc' : ∀ w, thetaEquiv e c' w = τ f • w := by
    intro w
    obtain ⟨u, rfl⟩ := hσ.2 w
    rw [hcompat c c' hcg u, hthc, map_smulₛₗ]
    rfl
  have hcent : centEnd c' = kappaA e (τ f) := by
    apply postcomp_injective e
    refine LinearMap.ext fun φ => LinearMap.ext fun i => ?_
    show (c' : GLV V) (φ i) = kappaA e (τ f) (φ i)
    rw [kappaA_comp]
    exact congrArg (fun ψ : I' →ₗ[HRing H] V => ψ i) (hthc' φ)
  ext v
  show g (kappaA e f v) = kappaA e (τ f) (g v)
  rw [← hcv, ← congrArg (fun T : Module.End (HRing H) V => T (g v)) hcent]
  show g ((c : GLV V) v) = (g * (c : GLV V) * g⁻¹) (g v)
  simp

end Conj

end Scalar

end E11

end G11

end CFSG.Quasithin

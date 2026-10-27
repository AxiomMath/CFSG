module

public import CFSG.Monster.IsolatedAxes
public import Mathlib.LinearAlgebra.Basis.Defs

public section

namespace CFSG.Monster

open Module

theorem finite_of_isolated_axes_basis {V : Type*} [AddCommGroup V] [Module ℚ V] {ι : Type*}
    [Fintype ι] (b : Basis ι ℚ V) (mul : V →ₗ[ℚ] V →ₗ[ℚ] V) (hcomm : ∀ u v, mul u v = mul v u)
    (d : ι → ℚ) (hd : ∀ i, 0 < d i) (Γ : Subgroup (V ≃ₗ[ℚ] V))
    (hΓmul : ∀ g ∈ Γ, ∀ u v, g (mul u v) = mul (g u) (g v))
    (hΓq : ∀ g ∈ Γ, ∀ v, ∑ i, d i * b.repr (g v) i ^ 2 = ∑ i, d i * b.repr v i ^ 2)
    {I : Type*} [Finite I] (a : I → V) (c : I → ℚ) (haa : ∀ i, mul (a i) (a i) = c i • a i)
    (hT : ∀ i, IsUnit ((2 : ℚ) • mul (a i) - c i • LinearMap.id : Module.End ℚ V))
    (hspan : Submodule.span ℚ (⋃ i, MulAction.orbit Γ (a i)) = ⊤) :
    (∀ i, (MulAction.orbit Γ (a i)).Finite) ∧ Finite Γ := by
  classical
  set N := Fintype.card ι
  set eι : ι ≃ Fin N := Fintype.equivFin ι
  set e : V ≃ₗ[ℚ] (Fin N → ℚ) := b.equivFun.trans (LinearEquiv.funCongrLeft ℚ ℚ eι.symm) with he
  have e_apply : ∀ v j, e v j = b.repr v (eι.symm j) := fun v j => rfl
  set mul' : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) :=
    (mul.compl₁₂ (e.symm : (Fin N → ℚ) →ₗ[ℚ] V) (e.symm : (Fin N → ℚ) →ₗ[ℚ] V)).compr₂
      (e : V →ₗ[ℚ] (Fin N → ℚ)) with hmul'
  have mul'_apply : ∀ u v, mul' u v = e (mul (e.symm u) (e.symm v)) := fun _ _ => rfl
  let conj : (V ≃ₗ[ℚ] V) →* ((Fin N → ℚ) ≃ₗ[ℚ] (Fin N → ℚ)) :=
    { toFun := fun g => e.symm.trans (g.trans e)
      map_one' := LinearEquiv.ext fun x => by simp
      map_mul' := fun g h => LinearEquiv.ext fun x => by simp [LinearEquiv.mul_apply] }
  have conj_apply : ∀ g x, conj g x = e (g (e.symm x)) := fun _ _ => rfl
  have conj_inj : Function.Injective conj := fun g h hgh => LinearEquiv.ext fun v => by
    have := congrArg (fun f : (Fin N → ℚ) ≃ₗ[ℚ] (Fin N → ℚ) => f (e v)) hgh
    simp only [conj_apply, LinearEquiv.symm_apply_apply] at this
    exact e.injective this
  set Γ' := Γ.map conj
  have hcomm' : ∀ u v, mul' u v = mul' v u := fun u v => by rw [mul'_apply, mul'_apply, hcomm]
  have hd' : ∀ j, 0 < d (eι.symm j) := fun j => hd _
  have hΓmul' : ∀ g ∈ Γ', ∀ u v, g (mul' u v) = mul' (g u) (g v) := by
    rintro _ ⟨g, hg, rfl⟩ u v
    simp only [conj_apply, mul'_apply, LinearEquiv.symm_apply_apply, hΓmul g hg]
  have hΓq' : ∀ g ∈ Γ', ∀ v, ∑ j, d (eι.symm j) * g v j ^ 2 = ∑ j, d (eι.symm j) * v j ^ 2 := by
    rintro _ ⟨g, hg, rfl⟩ v
    have h1 : ∑ j, d (eι.symm j) * (conj g) v j ^ 2 =
        ∑ i, d i * b.repr (g (e.symm v)) i ^ 2 := by
      rw [← eι.symm.sum_comp]
      rfl
    have h2 : ∑ j, d (eι.symm j) * v j ^ 2 = ∑ i, d i * b.repr (e.symm v) i ^ 2 := by
      rw [← eι.symm.sum_comp]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      have := e_apply (e.symm v) j
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
    rw [h1, h2, hΓq g hg]
  set a' : I → Fin N → ℚ := fun i => e (a i)
  have haa' : ∀ i, mul' (a' i) (a' i) = c i • a' i := fun i => by
    simp only [a', mul'_apply, LinearEquiv.symm_apply_apply, haa, map_smul]
  have hT' : ∀ i, IsUnit ((2 : ℚ) • mul' (a' i) - c i • LinearMap.id :
      Module.End ℚ (Fin N → ℚ)) := by
    intro i
    have hconj : ((2 : ℚ) • mul' (a' i) - c i • LinearMap.id : Module.End ℚ (Fin N → ℚ)) =
        LinearEquiv.conjRingEquiv e ((2 : ℚ) • mul (a i) - c i • LinearMap.id) := by
      refine LinearMap.ext fun x => ?_
      show _ = e ((((2 : ℚ) • mul (a i) - c i • LinearMap.id : Module.End ℚ V)) (e.symm x))
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, a', mul'_apply,
        LinearEquiv.symm_apply_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rw [hconj]
    exact (hT i).map (LinearEquiv.conjRingEquiv e)
  have horbit : ∀ i, MulAction.orbit Γ' (a' i) = e '' MulAction.orbit Γ (a i) := by
    intro i
    ext x
    constructor
    · rintro ⟨⟨_, g, hg, rfl⟩, rfl⟩
      exact ⟨g (a i), ⟨⟨g, hg⟩, rfl⟩, by
        change e (g (a i)) = conj g (e (a i))
        rw [conj_apply, LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
      exact ⟨⟨conj g, g, hg, rfl⟩, by
        change conj g (e (a i)) = e (g (a i))
        rw [conj_apply, LinearEquiv.symm_apply_apply]⟩
  have hspan' : Submodule.span ℚ (⋃ i, MulAction.orbit Γ' (a' i)) = ⊤ := by
    have : (⋃ i, MulAction.orbit Γ' (a' i)) = e '' ⋃ i, MulAction.orbit Γ (a i) := by
      rw [Set.image_iUnion]
      exact Set.iUnion_congr horbit
    rw [this]
    have hmap := Submodule.map_span (e : V →ₗ[ℚ] (Fin N → ℚ)) (⋃ i, MulAction.orbit Γ (a i))
    rw [LinearEquiv.coe_coe] at hmap
    rw [← hmap, hspan, Submodule.map_top, LinearEquiv.range]
  obtain ⟨hfin, hΓfin⟩ := finite_of_isolated_axes mul' hcomm' (fun j => d (eι.symm j)) hd' Γ'
    hΓmul' hΓq' a' c haa' hT' hspan'
  refine ⟨fun i => ?_, ?_⟩
  · have h := (hfin i).image e.symm
    rw [horbit, Set.image_image] at h
    simpa only [LinearEquiv.symm_apply_apply, Set.image_id'] using h
  · have : Finite Γ' := hΓfin
    exact Finite.of_injective (fun g : Γ => (⟨conj g, g, g.2, rfl⟩ : Γ'))
      fun g h hgh => Subtype.ext (conj_inj (congrArg Subtype.val hgh))

end CFSG.Monster

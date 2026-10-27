module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Ovg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SzPS8

section Sylow

theorem isSylowTwoOf_map_of_injective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {S H : Subgroup G} (h : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.map f) (H.map f) := by
  obtain ⟨hle, hp, hidx⟩ := h
  refine ⟨Subgroup.map_mono hle, hp.of_equiv (S.equivMapOfInjective f hf), ?_⟩
  show ¬ 2 ∣ (S.map f).relIndex (H.map f)
  rw [Subgroup.relIndex_map_map_of_injective S H hf]
  exact hidx

end Sylow

section Transport

variable {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem OvgFix.mono {T0 N M : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V} (h : OvgFix T0 N v)
    (hMN : M ≤ N) : OvgFix T0 M v :=
  fun J hJM hJn hidx => h J (hJM.trans hMN) hJn hidx

theorem OvgFix.map {T0 N : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V} (h : OvgFix T0 N v)
    (c : (V ≃ₗ[ZMod 2] V) ≃* (W ≃ₗ[ZMod 2] W)) (e : V ≃ₗ[ZMod 2] W)
    (hc : ∀ (γ : V ≃ₗ[ZMod 2] V) (x : V), c γ (e x) = e (γ x)) :
    OvgFix (T0.map c.toMonoidHom) (N.map c.toMonoidHom) (e v) := by
  intro J' hJ'N hJ'n hidx α' hα'
  set J : Subgroup (V ≃ₗ[ZMod 2] V) := J'.comap c.toMonoidHom with hJ
  have hcsurj : Function.Surjective c.toMonoidHom := c.surjective
  have hJmap : J.map c.toMonoidHom = J' := Subgroup.map_comap_eq_self_of_surjective hcsurj J'
  have hJN : J ≤ N := by
    intro j hj
    obtain ⟨n, hn, hnj⟩ := hJ'N hj
    have : n = j := c.injective hnj
    exact this ▸ hn
  have hJn : ∀ t ∈ T0, ∀ j ∈ J, t * j * t⁻¹ ∈ J := by
    intro t ht j hj
    show c (t * j * t⁻¹) ∈ J'
    rw [map_mul, map_mul, map_inv]
    exact hJ'n _ (Subgroup.mem_map_of_mem c.toMonoidHom ht) _ hj
  have hidxJ : T0.relIndex J = 3 ∨ T0.relIndex J = 5 := by
    have h1 := Subgroup.relIndex_map_map_of_injective T0 J
      (f := c.toMonoidHom) c.injective
    rw [hJmap] at h1
    rw [← h1]
    exact hidx
  have hα : c.symm α' ∈ J := by
    show c (c.symm α') ∈ J'
    rw [MulEquiv.apply_symm_apply]
    exact hα'
  have h2 := h J hJN hJn hidxJ _ hα
  have h3 : c.symm α' v = v := h2
  have h4 : α' (e v) = e v := by
    have := hc (c.symm α') v
    rw [MulEquiv.apply_symm_apply] at this
    rw [this, h3]
  exact h4

theorem OvgFix.conj_of {T0 N T1 : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V} (h : OvgFix T0 N v)
    {γ : V ≃ₗ[ZMod 2] V} (hγN' : ∀ n ∈ N, γ⁻¹ * n * γ ∈ N)
    (hT1 : ∀ x, x ∈ T1 ↔ ∃ y ∈ T0, x = γ * y * γ⁻¹) : OvgFix T1 N (γ v) := by
  set c : (V ≃ₗ[ZMod 2] V) →* (V ≃ₗ[ZMod 2] V) := (MulAut.conj γ).toMonoidHom with hc
  have hcx : ∀ x, c x = γ * x * γ⁻¹ := fun x => rfl
  have hcinj : Function.Injective c := (MulAut.conj γ).injective
  have hcsurj : Function.Surjective c := (MulAut.conj γ).surjective
  have hT : T0.map c = T1 := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hT1 _).mpr ⟨y, hy, hcx y⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (hT1 x).mp hx
      exact ⟨y, hy, hcx y⟩
  intro J' hJ'N hJ'n hidx α' hα'
  set J : Subgroup (V ≃ₗ[ZMod 2] V) := J'.comap c with hJ
  have hJN : J ≤ N := by
    intro j hj
    have h2 := hγN' _ (hJ'N hj)
    rw [hcx] at h2
    simpa [mul_assoc] using h2
  have hJn : ∀ t ∈ T0, ∀ j ∈ J, t * j * t⁻¹ ∈ J := by
    intro t ht j hj
    show c (t * j * t⁻¹) ∈ J'
    rw [map_mul, map_mul, map_inv]
    exact hJ'n _ (hT ▸ Subgroup.mem_map_of_mem c ht) _ hj
  have hJmap : J.map c = J' := Subgroup.map_comap_eq_self_of_surjective hcsurj J'
  have hidxJ : T0.relIndex J = 3 ∨ T0.relIndex J = 5 := by
    have h1 := Subgroup.relIndex_map_map_of_injective T0 J hcinj
    rw [hT, hJmap] at h1
    rw [← h1]
    exact hidx
  have hα : γ⁻¹ * α' * γ ∈ J := by
    show c (γ⁻¹ * α' * γ) ∈ J'
    rw [hcx]
    simpa [mul_assoc] using hα'
  have h3 : (γ⁻¹ * α' * γ) v = v := h J hJN hJn hidxJ _ hα
  have h4 : γ ((γ⁻¹ * α' * γ) v) = γ v := by rw [h3]
  simpa [mul_assoc] using h4

end Transport

end SzPS8

end CFSG.Quasithin

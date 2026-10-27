module

public import Mathlib.RepresentationTheory.Maschke

public section

namespace CFSG.Quasithin.RonanG52

lemma sum_inv_conj_apply {k G V : Type} [Field k] [Group G] [Fintype G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (φ : V →ₗ[k] V)
    (h : ∑ g : G, ρ g ∘ₗ φ ∘ₗ ρ g⁻¹ = LinearMap.id) (m : V) :
    ∑ x : G, ρ x⁻¹ (φ (ρ x m)) = m := by
  have hm := LinearMap.congr_fun h m
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at hm
  refine Eq.trans ?_ hm
  refine Fintype.sum_equiv (Equiv.inv G) _ _ (fun x => ?_)
  simp only [Equiv.inv_apply, inv_inv]

theorem projective_asModule_of_higman {k G V : Type} [Field k] [Group G] [Fintype G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (φ : V →ₗ[k] V)
    (h : ∑ g : G, ρ g ∘ₗ φ ∘ₗ ρ g⁻¹ = LinearMap.id) :
    Module.Projective (MonoidAlgebra k G) ρ.asModule := by
  apply Module.Projective.of_lifting_property
  intro M N _ _ _ _ f g hf
  letI : Module k M := Module.compHom M (algebraMap k (MonoidAlgebra k G))
  letI : Module k N := Module.compHom N (algebraMap k (MonoidAlgebra k G))
  haveI : IsScalarTower k (MonoidAlgebra k G) M := IsScalarTower.of_compHom k _ M
  haveI : IsScalarTower k (MonoidAlgebra k G) N := IsScalarTower.of_compHom k _ N
  obtain ⟨h₀, hh₀⟩ :=
    Module.projective_lifting_property (f.restrictScalars k) (g.restrictScalars k) hf
  have key : ∀ y : ρ.asModule, f (h₀ y) = g y := fun y => LinearMap.congr_fun hh₀ y
  obtain ⟨φ', hφ'⟩ : ∃ ψ : ρ.asModule →ₗ[k] ρ.asModule, ∀ y : V, ψ y = φ y :=
    ⟨φ, fun _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ q : ρ.asModule →ₗ[k] M, ∀ y, q y = h₀ (φ' y) :=
    ⟨h₀ ∘ₗ φ', fun _ => rfl⟩
  have hsmul : ∀ (x : G) (v : ρ.asModule), MonoidAlgebra.single x (1 : k) • v = ρ x v := by
    intro x v
    rw [Representation.single_smul, one_smul]
    rfl
  refine ⟨p.sumOfConjugatesEquivariant G, LinearMap.ext fun m => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.sumOfConjugatesEquivariant_apply, map_sum]
  have hterm : ∀ x : G, f (p.conjugate x m) =
      g (MonoidAlgebra.single x⁻¹ (1 : k) • φ' (MonoidAlgebra.single x (1 : k) • m)) := by
    intro x
    rw [LinearMap.conjugate_apply, map_smul f, hp, key, map_smul g]
  have hsum : ∑ x : G, MonoidAlgebra.single x⁻¹ (1 : k) • φ' (MonoidAlgebra.single x (1 : k) • m)
      = m := by
    have hid := sum_inv_conj_apply ρ φ h m
    simp only [hsmul]
    simp only [hφ']
    exact hid
  simp only [hterm]
  rw [← map_sum, hsum]

end CFSG.Quasithin.RonanG52

module

public import CFSG.ClassicalGroups.SpecialLinear.TvModLinAlg

public section

namespace CFSG.LinearAlgebra

open scoped commutatorElement

theorem linearEquivHom_eq_one_of_perfect_commute_nonscalar
    {G : Type*} [Group G] [Group.IsPerfect G]
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (hdim : Module.finrank F V = 2) (ρ : G →* (V ≃ₗ[F] V))
    {a : Module.End F V} (ha : ∀ c : F, a ≠ c • (1 : Module.End F V))
    (hcomm : ∀ g : G, Commute a (ρ g).toLinearMap) (g : G) : ρ g = 1 := by
  have hmul : ∀ x y : G, ρ x * ρ y = ρ y * ρ x := by
    intro x y
    have h := CFSG.ClassicalGroups.SpecialLinear.TvMod.commute_of_commute_of_finrank_eq_two
      hdim ha (hcomm x) (hcomm y)
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : Module.End F V => f v) h.eq
  have hker : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ ρ.ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hmul x y
  apply MonoidHom.mem_ker.mp
  apply hker
  rw [← commutator_def, Group.IsPerfect.commutator_eq_top]
  exact Subgroup.mem_top g

theorem fixes_plane_of_perfect_commute_nonscalar
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (P : Subgroup (V ≃ₗ[F] V)) [Group.IsPerfect P]
    (W : Submodule F V) (hdim : Module.finrank F W = 2)
    (a : V ≃ₗ[F] V)
    (hPW : ∀ g : P, ∀ w : W, (g : V ≃ₗ[F] V) (w : V) ∈ W)
    (haW : ∀ w : W, a (w : V) ∈ W)
    (hNS : ∀ c : F, ∃ w : W, a (w : V) ≠ c • (w : V))
    (hcomm : ∀ g : P, Commute a (g : V ≃ₗ[F] V)) :
    ∀ g : P, ∀ w : W, (g : V ≃ₗ[F] V) (w : V) = w := by
  let ρ : P →* (W ≃ₗ[F] W) :=
    { toFun := fun g =>
        { toFun := fun w => ⟨(g : V ≃ₗ[F] V) (w : V), hPW g w⟩
          invFun := fun w => ⟨((g⁻¹ : P) : V ≃ₗ[F] V) (w : V), hPW g⁻¹ w⟩
          left_inv := fun w => by
            apply Subtype.ext
            exact (g : V ≃ₗ[F] V).symm_apply_apply (w : V)
          right_inv := fun w => by
            apply Subtype.ext
            exact (g : V ≃ₗ[F] V).apply_symm_apply (w : V)
          map_add' := fun w v => by
            apply Subtype.ext
            exact (g : V ≃ₗ[F] V).map_add (w : V) (v : V)
          map_smul' := fun c w => by
            apply Subtype.ext
            exact (g : V ≃ₗ[F] V).map_smul c (w : V) }
      map_one' := by apply LinearEquiv.ext; intro w; apply Subtype.ext; rfl
      map_mul' := fun g h => by apply LinearEquiv.ext; intro w; apply Subtype.ext; rfl }
  let aW : Module.End F W :=
    { toFun := fun w => ⟨a (w : V), haW w⟩
      map_add' := fun w v => by apply Subtype.ext; exact a.map_add (w : V) (v : V)
      map_smul' := fun c w => by apply Subtype.ext; exact a.map_smul c (w : V) }
  have ha : ∀ c : F, aW ≠ c • (1 : Module.End F W) := by
    intro c h
    obtain ⟨w, hw⟩ := hNS c
    apply hw
    exact congrArg (fun f : Module.End F W => (f w : V)) h
  have hρ : ∀ g : P, Commute aW (ρ g).toLinearMap := by
    intro g
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact congrArg (fun f : V ≃ₗ[F] V => f (w : V)) (hcomm g).eq
  intro g w
  have h := linearEquivHom_eq_one_of_perfect_commute_nonscalar hdim ρ ha hρ g
  exact congrArg (fun f : W ≃ₗ[F] W => (f w : V)) h

end CFSG.LinearAlgebra

end

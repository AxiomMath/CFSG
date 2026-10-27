module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3GammaL

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def restrictL (L : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (g : L) : W →ₗ[K] W :=
  LinearMap.restrict (g.1 : V →ₗ[K] V) (hW g.1 g.2)

theorem restrictL_one (L : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) : restrictL L W hW 1 = LinearMap.id :=
  LinearMap.ext fun _ => rfl

theorem restrictL_mul (L : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (g h : L) :
    restrictL L W hW (g * h) = restrictL L W hW g * restrictL L W hW h :=
  LinearMap.ext fun _ => rfl

theorem restrictL_scalar (L : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (c : Kˣ) (hc : scalarHom K V c ∈ L) :
    restrictL L W hW ⟨scalarHom K V c, hc⟩ = (c : K) • LinearMap.id :=
  LinearMap.ext fun _ => Subtype.ext rfl

@[expose] noncomputable def detRestrictHom (L : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) : L →* K where
  toFun g := LinearMap.det (restrictL L W hW g)
  map_one' := by rw [restrictL_one, LinearMap.det_id]
  map_mul' g h := by rw [restrictL_mul, map_mul]

theorem detRestrictHom_scalar [FiniteDimensional K V] (L : Subgroup (V ≃ₗ[K] V))
    (W : Submodule K V) (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (c : Kˣ)
    (hc : scalarHom K V c ∈ L) :
    detRestrictHom L W hW ⟨scalarHom K V c, hc⟩ = (c : K) ^ Module.finrank K W := by
  show LinearMap.det (restrictL L W hW ⟨scalarHom K V c, hc⟩) = _
  rw [restrictL_scalar, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem irreducible_of_perfect_scalar [FiniteDimensional K V] (hV : Module.finrank K V = 3)
    (L : Subgroup (V ≃ₗ[K] V)) (hperf : Group.IsPerfect L) (c : Kˣ) (hc : scalarHom K V c ∈ L)
    (h1 : (c : K) ≠ 1) (h2 : (c : K) ^ 2 ≠ 1) :
    ∀ W : Submodule K V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  by_contra hne
  push Not at hne
  obtain ⟨hbot, htop⟩ := hne
  have hr0 : Module.finrank K W ≠ 0 := fun h => hbot (Submodule.finrank_eq_zero.1 h)
  have hr3 : Module.finrank K W ≠ 3 := fun h =>
    htop (Submodule.eq_top_of_finrank_eq (h.trans hV.symm))
  have hr4 : Module.finrank K W ≤ 3 := hV ▸ Submodule.finrank_le W
  have hχ : ∀ g : L, detRestrictHom L W hW g = 1 := by
    intro g
    have hk := Abelianization.commutator_subset_ker (detRestrictHom L W hW).toHomUnits
    rw [Group.isPerfect_def.1 hperf] at hk
    have := (MonoidHom.mem_ker).1 (hk (Subgroup.mem_top g))
    exact congrArg Units.val this
  have hcs := detRestrictHom_scalar L W hW c hc
  rw [hχ ⟨scalarHom K V c, hc⟩] at hcs
  have : Module.finrank K W = 1 ∨ Module.finrank K W = 2 := by omega
  rcases this with h | h
  · rw [h, pow_one] at hcs
    exact h1 hcs.symm
  · rw [h] at hcs
    exact h2 hcs.symm

end CFSG.Quasithin.D35Core

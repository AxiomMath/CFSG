module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin.JonesParshall

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {Γ W V : Type*} [Group Γ] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup V] [Module (ZMod 2) V]

private theorem bilin_apply_inv {ρ : Representation (ZMod 2) Γ W}
    {B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2}
    (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y) (g : Γ) (x y : W) :
    B (ρ g x) y = B x (ρ (g⁻¹) y) := by
  have h := hB g x (ρ (g⁻¹) y)
  simpa using h

section FiniteW

variable [Finite W]

private noncomputable def formDualEquiv
    (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0) :
    W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) W := by
  classical
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  refine LinearEquiv.ofInjectiveOfFinrankEq B ?_ ?_
  · intro x y hxy
    have h0 : B (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hxy0 : x - y = 0 := hBnd (x - y) fun z => by
      have hz := LinearMap.congr_fun h0 z
      simpa using hz
    exact sub_eq_zero.mp hxy0
  · exact (Subspace.dual_finrank_eq).symm

private theorem formDualEquiv_apply
    (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0) (x : W) :
    formDualEquiv B hBnd x = B x := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  rw [formDualEquiv]
  exact LinearMap.congr_fun
    (LinearEquiv.coe_ofInjectiveOfFinrankEq B _ (Subspace.dual_finrank_eq).symm) x

end FiniteW

private theorem linearEquiv_invariant
    (ρ : Representation (ZMod 2) Γ W) (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (ι : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) W) (hι : ∀ x, ι x = B x)
    (g : Γ) (x : W) : ι (ρ g x) = (ι x).comp (ρ (g⁻¹)) := by
  refine LinearMap.ext fun y => ?_
  rw [hι, hι, LinearMap.comp_apply]
  exact bilin_apply_inv hB g x y

private theorem coordCocycle_mem_Z1
    (ρ : Representation (ZMod 2) Γ W) (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (ι : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) W) (hι : ∀ x, ι x = B x)
    {D : Γ → (W →ₗ[ZMod 2] V)}
    (hD : D ∈ Z1 (ρ.linHom (Representation.trivial (ZMod 2) Γ V)))
    (c : V →ₗ[ZMod 2] ZMod 2) :
    (fun g => ι.symm (c.comp (D g))) ∈ Z1 ρ := by
  intro g h
  apply ι.injective
  rw [map_add, LinearEquiv.apply_symm_apply]
  rw [linearEquiv_invariant ρ B hB ι hι g (ι.symm (c.comp (D h)))]
  simp only [LinearEquiv.apply_symm_apply]
  have hstep : D (g * h) = D g + (D h).comp (ρ (g⁻¹)) := by
    have hDgh := hD g h
    rw [Representation.linHom_apply,
      Representation.isTrivial_def (Representation.trivial (ZMod 2) Γ V) g,
      LinearMap.id_comp] at hDgh
    exact hDgh
  rw [hstep, LinearMap.comp_add]
  simp only [LinearMap.comp_assoc]

theorem mem_B1_linHom_trivial [Finite W] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) Γ W) (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hH1 : ∀ φ : Γ → W, φ ∈ Z1 ρ → φ ∈ B1 ρ) {D : Γ → (W →ₗ[ZMod 2] V)}
    (hD : D ∈ Z1 (ρ.linHom (Representation.trivial (ZMod 2) Γ V))) :
    D ∈ B1 (ρ.linHom (Representation.trivial (ZMod 2) Γ V)) := by
  classical
  let ι := formDualEquiv B hBnd
  have hι : ∀ x, ι x = B x := formDualEquiv_apply B hBnd
  let b := Module.finBasis (ZMod 2) V
  have hψ : ∀ j, (fun g => ι.symm ((b.coord j).comp (D g))) ∈ Z1 ρ :=
    fun j => coordCocycle_mem_Z1 ρ B hB ι hι hD (b.coord j)
  have hchoice : ∀ j, ∃ w : W, coboundary ρ w =
      (fun g => ι.symm ((b.coord j).comp (D g))) :=
    fun j => hH1 _ (hψ j)
  choose w hw using hchoice
  have hDcoord : ∀ (j : Fin (Module.finrank (ZMod 2) V)) (g : Γ) (x : W),
      (b.coord j) (D g x) = B (w j) (ρ (g⁻¹) x) - B (w j) x := by
    intro j g x
    have h := congrFun (hw j) g
    have h2 := congrArg ι h
    rw [LinearEquiv.apply_symm_apply] at h2
    change ι (ρ g (w j) - w j) = (b.coord j).comp (D g) at h2
    have h3 := LinearMap.congr_fun h2 x
    rw [hι (ρ g (w j) - w j), map_sub, LinearMap.sub_apply,
      LinearMap.comp_apply, bilin_apply_inv hB] at h3
    exact h3.symm
  let φ : W →ₗ[ZMod 2] V := ∑ j, (B (w j)).smulRight (b j)
  have hφ : ∀ (j : Fin (Module.finrank (ZMod 2) V)) (y : W),
      (b.coord j) (φ y) = B (w j) y := by
    intro j y
    have hsum : φ y = ∑ k, B (w k) y • b k := by
      simp [φ, LinearMap.smulRight_apply]
    rw [hsum, map_sum]
    rw [Finset.sum_eq_single j]
    · rw [map_smul, b.coord_apply, b.repr_self_apply]
      simp
    · intro k _ hkj
      rw [map_smul, b.coord_apply, b.repr_self_apply]
      simp [hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  refine ⟨φ, ?_⟩
  funext g
  refine LinearMap.ext fun x => ?_
  refine b.ext_elem fun j => ?_
  rw [← b.coord_apply, ← b.coord_apply]
  have hσ : (ρ.linHom (Representation.trivial (ZMod 2) Γ V)) g φ =
      φ.comp (ρ (g⁻¹)) := by
    rw [Representation.linHom_apply,
      Representation.isTrivial_def (Representation.trivial (ZMod 2) Γ V) g,
      LinearMap.id_comp]
  change (b.coord j) (((ρ.linHom (Representation.trivial (ZMod 2) Γ V)) g φ - φ) x) =
    (b.coord j) (D g x)
  rw [hσ, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hφ, hφ, hDcoord]

end CFSG.Quasithin.F112R.St84

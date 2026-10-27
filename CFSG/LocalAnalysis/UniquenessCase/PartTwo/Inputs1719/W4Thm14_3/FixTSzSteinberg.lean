module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin.JonesParshall

theorem mem_B1_dual_of_higman {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) {U : Subgroup G} [Fintype ↥U]
    (hU : Odd U.index) (φ : V →ₗ[ZMod 2] V) (hφ : ∀ x, ∑ u : ↥U, ρ u (φ (ρ ((u : G)⁻¹) x)) = x)
    {c : G → Module.Dual (ZMod 2) V} (hc : c ∈ Z1 ρ.dual) : c ∈ B1 ρ.dual := by
  classical
  let μ : G →* AddMonoid.End (Module.Dual (ZMod 2) V) :=
    { toFun := fun g => (ρ.dual g).toAddMonoidHom
      map_one' := by
        ext f x
        change (ρ.dual 1 f) x = f x
        rw [Representation.dual_apply, Module.Dual.transpose_apply]
        simp
      map_mul' := fun g h => by
        ext f x
        change (ρ.dual (g * h) f) x = (ρ.dual g (ρ.dual h f)) x
        rw [map_mul]
        rfl }
  let ψ : Module.Dual (ZMod 2) V →ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
    Module.Dual.transpose φ
  have hμ : ∀ (g : G) (f : Module.Dual (ZMod 2) V) (x : V),
      (μ g f) x = f (ρ g⁻¹ x) := by
    intro g f x
    change (ρ.dual g f) x = f (ρ g⁻¹ x)
    rw [Representation.dual_apply, Module.Dual.transpose_apply]
    rfl
  have hψ : ∀ (f : Module.Dual (ZMod 2) V) (x : V), (ψ f) x = f (φ x) := by
    intro f x
    change (Module.Dual.transpose φ f) x = f (φ x)
    rw [Module.Dual.transpose_apply]
    rfl
  have hμmul : ∀ (a b : G) (m : Module.Dual (ZMod 2) V),
      μ (a * b) m = μ a (μ b m) := by
    intro a b m
    rw [map_mul]
    rfl
  have h2 : ∀ m : Module.Dual (ZMod 2) V, m + m = 0 := by
    intro m
    ext x
    exact CharTwo.add_self_eq_zero (m x)
  have hZ : c ∈ Z1A μ := hc
  have hc_one : c 1 = 0 := Z1A_one hZ
  have hneg : ∀ m : Module.Dual (ZMod 2) V, -m = m :=
    fun m => neg_eq_of_add_eq_zero_left (h2 m)
  have hc_inv : ∀ u : G, c u⁻¹ = μ u⁻¹ (c u) := by
    intro u
    have h : c u⁻¹ + μ u⁻¹ (c u) = 0 := by
      have h1 := hZ u⁻¹ u
      rw [inv_mul_cancel, hc_one] at h1
      exact h1.symm
    calc c u⁻¹ = - μ u⁻¹ (c u) := eq_neg_of_add_eq_zero_left h
      _ = μ u⁻¹ (c u) := hneg _
  have hφd : ∀ f : Module.Dual (ZMod 2) V,
      ∑ u : ↥U, μ (u : G) (ψ (μ ((u : G)⁻¹) f)) = f := by
    intro f
    ext x
    rw [LinearMap.sum_apply]
    have hterm : ∀ u : ↥U,
        (μ (u : G) (ψ (μ ((u : G)⁻¹) f))) x =
          f (ρ (u : G) (φ (ρ ((u : G)⁻¹) x))) := by
      intro u
      rw [hμ, hψ, hμ]
      simp
    rw [Finset.sum_congr rfl fun u _ => hterm u]
    rw [← map_sum]
    exact congrArg f (hφ x)
  let v : Module.Dual (ZMod 2) V :=
    ∑ w : ↥U, μ (w : G) (ψ (μ ((w : G)⁻¹) (c (w : G))))
  have hμv : ∀ u : G,
      μ u v = ∑ w : ↥U, μ (u * (w : G)) (ψ (μ ((w : G)⁻¹) (c (w : G)))) := by
    intro u
    simp only [v, map_sum, ← hμmul]
  have hsummand : ∀ (u : G) (w : ↥U),
      μ (w : G) (ψ (μ ((w : G)⁻¹ * u) (c (u⁻¹ * (w : G))))) =
        μ (w : G) (ψ (μ (w : G)⁻¹ (c (w : G)))) +
          μ (w : G) (ψ (μ (w : G)⁻¹ (c u))) := by
    intro u w
    have h1 : μ ((w : G)⁻¹ * u) (c (u⁻¹ * (w : G))) =
        μ ((w : G)⁻¹) (c (w : G)) + μ ((w : G)⁻¹) (c u) := by
      rw [hZ u⁻¹ (w : G), hc_inv u]
      simp only [map_add]
      rw [← hμmul, ← hμmul]
      rw [show (w : G)⁻¹ * u * u⁻¹ = (w : G)⁻¹ by group]
      rw [add_comm]
    rw [h1]
    simp only [map_add]
  have hstep : ∀ u : ↥U, μ (u : G) v = v + c (u : G) := by
    intro u
    have hre : (∑ w : ↥U,
          μ ((u : G) * (w : G)) (ψ (μ ((w : G)⁻¹) (c (w : G))))) =
        ∑ w : ↥U, μ (w : G) (ψ (μ ((w : G)⁻¹ * (u : G)) (c ((u : G)⁻¹ * (w : G))))) := by
      let e : Equiv.Perm ↥U := Equiv.mulLeft u
      let g : ↥U → Module.Dual (ZMod 2) V := fun w =>
        μ (w : G) (ψ (μ ((w : G)⁻¹ * (u : G)) (c ((u : G)⁻¹ * (w : G)))))
      have h := Equiv.sum_comp e g
      rw [← h]
      apply Finset.sum_congr rfl
      intro w _
      have he : ((e w : ↥U) : G) = (u : G) * (w : G) := rfl
      dsimp only [g]
      rw [he]
      show μ ((u : G) * (w : G)) (ψ (μ ((w : G)⁻¹) (c (w : G)))) =
        μ ((u : G) * (w : G)) (ψ (μ (((u : G) * (w : G))⁻¹ * (u : G))
          (c ((u : G)⁻¹ * ((u : G) * (w : G))))))
      rw [show ((u : G) * (w : G))⁻¹ * (u : G) = (w : G)⁻¹ by group,
        show (u : G)⁻¹ * ((u : G) * (w : G)) = (w : G) by group]
    rw [hμv u, hre]
    rw [Finset.sum_congr rfl fun w _ => hsummand (u : G) w]
    rw [Finset.sum_add_distrib]
    rw [show (∑ w : ↥U, μ (w : G) (ψ (μ ((w : G)⁻¹) (c (w : G))))) = v from rfl]
    rw [hφd]
  have hrestrict : ∀ u ∈ U, c u = μ u v - v := by
    intro u hu
    have h := hstep ⟨u, hu⟩
    rw [h]
    abel
  have hB := mem_B1A_of_restrict (μ := μ) h2 hU hZ (m := v) hrestrict
  obtain ⟨m, hm⟩ := hB
  exact ⟨m, by rw [← hm]; rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

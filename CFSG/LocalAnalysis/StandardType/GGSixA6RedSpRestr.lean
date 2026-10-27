module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpDefs

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

theorem ggA6_sp_restr_equiv {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Finite F] [CharP F 2] [FiniteDimensional F V] (B : BilinForm F V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (U : Submodule F V) (hU : (B.restrict U).Nondegenerate) :
    ∃ e : ggA6SpFixer B (B.orthogonal U) ≃* TauCeti.BilinForm.isometryGroup (B.restrict U),
      ∀ (g : ggA6SpFixer B (B.orthogonal U)) (u : U),
        ((e g : U ≃ₗ[F] U) u : V) = (g : V ≃ₗ[F] V) u := by
  classical
  have mapsTo : ∀ g ∈ ggA6SpFixer B (B.orthogonal U), ∀ u ∈ U, g u ∈ U := by
    intro g hg u hu
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl U,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    have hx' : (g : V ≃ₗ[F] V).symm x = x :=
      ((ggA6SpFixer B (B.orthogonal U)).inv_mem hg).2 x hx
    have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.mp hg.1 ((g : V ≃ₗ[F] V).symm x) u
    rw [LinearEquiv.apply_symm_apply, hx'] at hiso
    rw [hiso]
    exact hB.eq_iff.mpr ((LinearMap.BilinForm.mem_orthogonal_iff.mp hx) u hu)
  let restr : ggA6SpFixer B (B.orthogonal U) →* (U ≃ₗ[F] U) :=
    { toFun := fun g => (g : V ≃ₗ[F] V).ofSubmodules U U (by
        refine le_antisymm (fun w hw => ?_) (fun w hw => ?_)
        · obtain ⟨u, hu, rfl⟩ := hw
          exact mapsTo g g.2 u hu
        · exact ⟨(g : V ≃ₗ[F] V).symm w,
            mapsTo ((g : V ≃ₗ[F] V).symm) ((ggA6SpFixer B (B.orthogonal U)).inv_mem g.2) w hw, by
              show (g : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V).symm w) = w
              rw [LinearEquiv.apply_symm_apply]⟩)
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have restr_coe : ∀ (g : ggA6SpFixer B (B.orthogonal U)) (u : U),
      ((restr g : U ≃ₗ[F] U) u : V) = (g : V ≃ₗ[F] V) u := fun _ _ => rfl
  have restr_mem : ∀ g : ggA6SpFixer B (B.orthogonal U),
      restr g ∈ TauCeti.BilinForm.isometryGroup (B.restrict U) := by
    intro g
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro u v
    show B ((restr g) u : V) ((restr g) v : V) = B (u : V) (v : V)
    rw [restr_coe, restr_coe]
    exact TauCeti.BilinForm.mem_isometryGroup_iff.mp g.2.1 u v
  let φ : ggA6SpFixer B (B.orthogonal U) →* TauCeti.BilinForm.isometryGroup (B.restrict U) :=
    restr.codRestrict _ restr_mem
  have φ_coe_apply : ∀ (g : ggA6SpFixer B (B.orthogonal U)) (u : U),
      ((φ g : U ≃ₗ[F] U) u : V) = (g : V ≃ₗ[F] V) u := fun g u => restr_coe g u
  have hc : IsCompl U (B.orthogonal U) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate (B := B) hB.isRefl hU
  have φ_inj : Function.Injective φ := by
    intro g h hgh
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    set y : U × (B.orthogonal U) :=
      (Submodule.prodEquivOfIsCompl U (B.orthogonal U) hc).symm v with hy
    have hv : v = (y.1 : V) + (y.2 : V) := by
      rw [← Submodule.coe_prodEquivOfIsCompl' U (B.orthogonal U) hc y, hy,
        LinearEquiv.apply_symm_apply]
    have hgu : (g : V ≃ₗ[F] V) (y.1 : V) = (h : V ≃ₗ[F] V) (y.1 : V) := by
      have h1 := congrArg (fun k : ↥(TauCeti.BilinForm.isometryGroup (B.restrict U)) =>
        (((k : U ≃ₗ[F] U) y.1 : U) : V)) hgh
      simpa only [φ_coe_apply] using h1
    have hgw : (g : V ≃ₗ[F] V) (y.2 : V) = (h : V ≃ₗ[F] V) (y.2 : V) := by
      rw [g.2.2 _ y.2.2, h.2.2 _ y.2.2]
    calc (g : V ≃ₗ[F] V) v
        = (g : V ≃ₗ[F] V) ((y.1 : V) + (y.2 : V)) := by conv_lhs => rw [hv]
      _ = (g : V ≃ₗ[F] V) (y.1 : V) + (g : V ≃ₗ[F] V) (y.2 : V) := map_add ..
      _ = (h : V ≃ₗ[F] V) (y.1 : V) + (h : V ≃ₗ[F] V) (y.2 : V) := by rw [hgu, hgw]
      _ = (h : V ≃ₗ[F] V) ((y.1 : V) + (y.2 : V)) := (map_add ..).symm
      _ = (h : V ≃ₗ[F] V) v := by conv_rhs => rw [hv]
  have φ_surj : Function.Surjective φ := by
    intro g'
    let G : V ≃ₗ[F] V :=
      (Submodule.prodEquivOfIsCompl U (B.orthogonal U) hc).symm.trans
        (((g' : U ≃ₗ[F] U).prodCongr (LinearEquiv.refl F (B.orthogonal U))).trans
          (Submodule.prodEquivOfIsCompl U (B.orthogonal U) hc))
    have ext_left : ∀ u : U, G (u : V) = ((g' : U ≃ₗ[F] U) u : V) := by
      intro u
      show (Submodule.prodEquivOfIsCompl U (B.orthogonal U) hc)
          (((g' : U ≃ₗ[F] U).prodCongr (LinearEquiv.refl F (B.orthogonal U)))
            ((Submodule.prodEquivOfIsCompl U (B.orthogonal U) hc).symm (u : V))) = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left, LinearEquiv.prodCongr_apply,
        Submodule.coe_prodEquivOfIsCompl', map_zero, Submodule.coe_zero, add_zero]
    have ext_right : ∀ w : B.orthogonal U, G (w : V) = (w : V) := by
      intro w
      show (Submodule.prodEquivOfIsCompl U (B.orthogonal U) hc)
          (((g' : U ≃ₗ[F] U).prodCongr (LinearEquiv.refl F (B.orthogonal U)))
            ((Submodule.prodEquivOfIsCompl U (B.orthogonal U) hc).symm (w : V))) = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_right, LinearEquiv.prodCongr_apply,
        LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl', map_zero, Submodule.coe_zero,
        zero_add]
    have ext_mem : G ∈ TauCeti.BilinForm.isometryGroup B := by
      rw [TauCeti.BilinForm.mem_isometryGroup_iff]
      intro x y
      set x' : U × (B.orthogonal U) :=
        (Submodule.prodEquivOfIsCompl U (B.orthogonal U) hc).symm x with hx'
      set y' : U × (B.orthogonal U) :=
        (Submodule.prodEquivOfIsCompl U (B.orthogonal U) hc).symm y with hy'
      have hx : x = (x'.1 : V) + (x'.2 : V) := by
        rw [← Submodule.coe_prodEquivOfIsCompl' U (B.orthogonal U) hc x', hx',
          LinearEquiv.apply_symm_apply]
      have hy : y = (y'.1 : V) + (y'.2 : V) := by
        rw [← Submodule.coe_prodEquivOfIsCompl' U (B.orthogonal U) hc y', hy',
          LinearEquiv.apply_symm_apply]
      have hgx : G x = (((g' : U ≃ₗ[F] U) x'.1 : U) : V) + (x'.2 : V) := by
        rw [hx, map_add, ext_left, ext_right]
      have hgy : G y = (((g' : U ≃ₗ[F] U) y'.1 : U) : V) + (y'.2 : V) := by
        rw [hy, map_add, ext_left, ext_right]
      have hB1 : B (((g' : U ≃ₗ[F] U) x'.1 : U) : V) (y'.2 : V) = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp y'.2.2) _ ((g' : U ≃ₗ[F] U) x'.1).2
      have hB2 : B (x'.2 : V) (((g' : U ≃ₗ[F] U) y'.1 : U) : V) = 0 :=
        hB.eq_iff.mpr ((LinearMap.BilinForm.mem_orthogonal_iff.mp x'.2.2) _
          ((g' : U ≃ₗ[F] U) y'.1).2)
      have hB3 : B (((g' : U ≃ₗ[F] U) x'.1 : U) : V) (((g' : U ≃ₗ[F] U) y'.1 : U) : V)
          = B (x'.1 : V) (y'.1 : V) :=
        TauCeti.BilinForm.mem_isometryGroup_iff.mp g'.2 x'.1 y'.1
      have hB4 : B (x'.1 : V) (y'.2 : V) = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp y'.2.2) _ x'.1.2
      have hB5 : B (x'.2 : V) (y'.1 : V) = 0 :=
        hB.eq_iff.mpr ((LinearMap.BilinForm.mem_orthogonal_iff.mp x'.2.2) _ y'.1.2)
      rw [hgx, hgy, hx, hy]
      simp only [map_add, LinearMap.add_apply, hB1, hB2, hB3, hB4, hB5, add_zero, zero_add]
      try abel
    refine ⟨⟨G, ?_⟩, ?_⟩
    · exact ⟨ext_mem, fun u hu => ext_right ⟨u, hu⟩⟩
    · refine Subtype.ext (LinearEquiv.ext fun u => Subtype.ext ?_)
      rw [φ_coe_apply, ext_left]
  exact ⟨MulEquiv.ofBijective φ ⟨φ_inj, φ_surj⟩, φ_coe_apply⟩

end CFSG.StandardType.A6Red

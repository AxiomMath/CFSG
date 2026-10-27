module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenDefs

import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder
import CFSG.LargeExtraspecial.S4Restrict
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryTwo
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthCentralizer
import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardClosure
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityAlternating
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthRestrict
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel

public section

open CFSG.ClassicalGroups CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial
open LinearMap (BilinForm)

namespace CFSG.StandardType.SpNsRootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {B : LinearMap.BilinForm F V}

private theorem gspFixPerp_mapsTo (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {U : Submodule F V} {g : Gsp B} (hg : g ∈ gspFixPerp B U) :
    ∀ u ∈ U, g.app u ∈ U := by
  intro u hu
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hBn hB.isRefl U,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  have hx' : g⁻¹.app x = x :=
    (mem_gspFixPerp.mp ((gspFixPerp B U).inv_mem hg)) x hx
  calc B x (g.app u)
      = B (g⁻¹.app x) (g⁻¹.app (g.app u)) := (Gsp.form_app g⁻¹ x (g.app u)).symm
    _ = B (g⁻¹.app x) u := by rw [Gsp.app_inv_app]
    _ = B x u := by rw [hx']
    _ = 0 := hB.eq_iff.mpr ((LinearMap.BilinForm.mem_orthogonal_iff.mp hx) u hu)

private noncomputable def restrictToPlane (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {U : Submodule F V} (hUn : (B.restrict U).Nondegenerate) :
    ↥(gspFixPerp B U) →* Gsp (B.restrict U) :=
  let φ : ↥(gspFixPerp B U) →* (V ≃ₗ[F] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp
      ((bilinIsometryGroup B).subtype.comp (gspFixPerp B U).subtype)
  let ψ : ↥(gspFixPerp B U) →* (U ≃ₗ[F] U) :=
    CFSG.LargeExtraspecial.S4.restrictHom φ U
      (fun x u hu => gspFixPerp_mapsTo hB hBn x.2 u hu)
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F U).symm.toMonoidHom.comp ψ).codRestrict
    (bilinIsometryGroup (B.restrict U)) (fun x => by
      rw [mem_bilinIsometryGroup]
      intro u v
      show B ((ψ x) u : V) ((ψ x) v : V) = B (u : V) (v : V)
      rw [show ((ψ x) u : V) = (x : Gsp B).app (u : V) from rfl,
        show ((ψ x) v : V) = (x : Gsp B).app (v : V) from rfl]
      exact (x : Gsp B).2 u v)

private theorem restrictToPlane_apply (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {U : Submodule F V} (hUn : (B.restrict U).Nondegenerate)
    (x : ↥(gspFixPerp B U)) (u : U) :
    (((restrictToPlane hB hBn hUn x).app u : U) : V) = (x : Gsp B).app (u : V) := rfl

private theorem restrictToPlane_injective (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {U : Submodule F V} (hUn : (B.restrict U).Nondegenerate) :
    Function.Injective (restrictToPlane hB hBn hUn) := by
  intro x y hxy
  refine Subtype.ext (Gsp.ext' fun v => ?_)
  obtain ⟨p, hp, w, hw, rfl⟩ :=
    exists_add_eq (LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      hB.isRefl hUn).symm v
  have hxw : (x : Gsp B).app w = (y : Gsp B).app w := by
    have h := congrArg (fun f : Gsp (B.restrict U) => (f.app ⟨w, hw⟩ : U)) hxy
    have h2 : (((restrictToPlane hB hBn hUn x).app ⟨w, hw⟩ : U) : V)
        = (((restrictToPlane hB hBn hUn y).app ⟨w, hw⟩ : U) : V) := congrArg Subtype.val h
    rwa [restrictToPlane_apply, restrictToPlane_apply] at h2
  have hxp : (x : Gsp B).app p = p := (mem_gspFixPerp.mp x.2) p hp
  have hyp : (y : Gsp B).app p = p := (mem_gspFixPerp.mp y.2) p hp
  rw [Gsp.map_add, Gsp.map_add, hxp, hyp, hxw]

private theorem restrictToPlane_surjective (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {U : Submodule F V} (hUn : (B.restrict U).Nondegenerate) :
    Function.Surjective (restrictToPlane hB hBn hUn) := by
  intro g'
  let hPW : IsCompl (B.orthogonal U) U :=
    (LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hUn).symm
  let horth : ∀ p ∈ B.orthogonal U, ∀ w ∈ U, B p w = 0 :=
    fun p hp w hw => hB.eq_iff.mpr ((LinearMap.BilinForm.mem_orthogonal_iff.mp hp) w hw)
  let g : Gsp B := extId hPW hB horth g'
  have hg : g ∈ gspFixPerp B U := by
    intro x hx
    exact extId_app_of_mem hPW hB horth g' hx
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Gsp.ext'
  intro u
  apply Subtype.ext
  rw [restrictToPlane_apply]
  have h0 : (0 : V) ∈ B.orthogonal U := Submodule.zero_mem _
  have h := extId_app hPW hB horth g' h0 u.2
  simpa using h

private noncomputable def gspFixPerpEquivPlane (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {U : Submodule F V} (hUn : (B.restrict U).Nondegenerate) :
    ↥(gspFixPerp B U) ≃* Gsp (B.restrict U) :=
  MulEquiv.ofBijective _ ⟨restrictToPlane_injective hB hBn hUn,
    restrictToPlane_surjective hB hBn hUn⟩

theorem nonempty_gspFixPerp_mulEquiv_SL (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {U : Submodule F V} (hU2 : Module.finrank F U = 2) (hUn : (B.restrict U).Nondegenerate) :
    Nonempty (↥(gspFixPerp B U) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨e⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_planeIsometryEquivSL
      (B.restrict U) (isAlt_restrict hB U) hUn hU2
  exact ⟨(gspFixPerpEquivPlane hB hBn hUn).trans
    ((CFSG.ComponentClassification.UnbalancedCatalog.bilinIsometryGroupEquiv (B.restrict U)).trans
      e)⟩

theorem isQuasisimple_gspFixPerp (hB : B.IsAlt) (hBn : B.Nondegenerate) {U : Submodule F V}
    (hU2 : Module.finrank F U = 2) (hUn : (B.restrict U).Nondegenerate) (hF4 : 4 ≤ Nat.card F) :
    CFSG.Assembly.IsQuasisimple ↥(gspFixPerp B U) := by
  obtain ⟨e⟩ := nonempty_gspFixPerp_mulEquiv_SL hB hBn hU2 hUn
  exact CFSG.LocalAnalysis.SymplecticFourStandard.RootStandard.isQuasisimple_of_sl2 hF4 e.symm

theorem exists_orderOf_eq_mem_gspFixPerp (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {U : Submodule F V} (hU2 : Module.finrank F U = 2) (hUn : (B.restrict U).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card F + 1) :
    ∃ g : Gsp B, g ∈ gspFixPerp B U ∧ orderOf g = p := by
  obtain ⟨e⟩ := nonempty_gspFixPerp_mulEquiv_SL hB hBn hU2 hUn
  have hdvd : p ∣ Nat.card F ^ 2 - 1 :=
    dvd_trans hpq ⟨Nat.card F - 1, by
      simpa using Nat.pow_two_sub_pow_two (Nat.card F) 1⟩
  obtain ⟨b, hb⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2
    (k := F) hp hdvd
  refine ⟨(e.symm b : ↥(gspFixPerp B U)), (e.symm b).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hb]

end CFSG.StandardType.SpNsRootGen

end

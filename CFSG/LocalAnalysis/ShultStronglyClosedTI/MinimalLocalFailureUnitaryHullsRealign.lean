module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsCoordinates
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedModel

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism CFSG.ShultStronglyClosedTI.UnitaryExcluded
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G]

@[expose] def conjInvolutionAut {L : Subgroup G} {u : G} (hu2 : u * u = 1)
    (huL : ∀ x ∈ L, u * x * u⁻¹ ∈ L) : MulAut L where
  toFun x := ⟨u * x * u⁻¹, huL x x.2⟩
  invFun x := ⟨u * x * u⁻¹, huL x x.2⟩
  left_inv x := Subtype.ext (by
    change u * (u * (x : G) * u⁻¹) * u⁻¹ = x
    rw [show u * (u * (x : G) * u⁻¹) * u⁻¹ = (u * u) * x * (u * u)⁻¹ by group, hu2, one_mul,
      inv_one, mul_one])
  right_inv x := Subtype.ext (by
    change u * (u * (x : G) * u⁻¹) * u⁻¹ = x
    rw [show u * (u * (x : G) * u⁻¹) * u⁻¹ = (u * u) * x * (u * u)⁻¹ by group, hu2, one_mul,
      inv_one, mul_one])
  map_mul' x y := Subtype.ext (by
    change u * ((x : G) * y) * u⁻¹ = u * x * u⁻¹ * (u * y * u⁻¹)
    group)

theorem coe_conjInvolutionAut {L : Subgroup G} {u : G} (hu2 : u * u = 1)
    (huL : ∀ x ∈ L, u * x * u⁻¹ ∈ L) (x : L) :
    ((conjInvolutionAut hu2 huL x : L) : G) = u * x * u⁻¹ :=
  rfl

theorem exists_bar_coordinates [Finite G] {H L : Subgroup G} {z t : G}
    {beta : rightCosetSpace H} (F : UnitaryHullCoordinates H z beta t L) {u : G}
    (hu2 : u * u = 1) (huL : ∀ x ∈ L, u * x * u⁻¹ ∈ L)
    (huK : ∀ x ∈ minimalLocalFailureProperPairHull H z beta t, u * x = x * u)
    (hnontriv : ∃ x ∈ L, u * x ≠ x * u) :
    ∃ φ : hermitianUnipotentCoord F.J ≃* F.root,
      (∀ w, (φ w : G) ∈ minimalLocalFailurePairActionPointHull H z ↔ w.1.1 = 0) ∧
      ∀ w, u * (φ w : G) * u⁻¹ = (φ (UnitaryRootAutomorphism.rootTau F.J w) : G) := by
  obtain ⟨cu, hcu⟩ : ∃ cu : MulAut L, ∀ x : L, (cu x : G) = u * x * u⁻¹ :=
    ⟨conjInvolutionAut hu2 huL, fun x => rfl⟩
  have hcu2 : ∀ y : L, cu (cu y) = y := fun y => Subtype.ext (by
    rw [hcu, hcu, show u * (u * (y : G) * u⁻¹) * u⁻¹ = (u * u) * y * (u * u)⁻¹ by group, hu2,
      one_mul, inv_one, mul_one])
  obtain ⟨σ, hσθ⟩ : ∃ σ : MulAut (F.J.specialSubgroup ⧸ F.C), ∀ x, F.θ (σ x) = cu (F.θ x) :=
    ⟨(F.θ.trans cu).trans F.θ.symm, fun x => by
      rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.trans_apply]⟩
  have hσfix : σ ∈ sublineFixingAut F.J F.C F.hJ := by
    rw [mem_sublineFixingAut]
    intro x hx
    apply F.θ.injective
    rw [hσθ]
    apply Subtype.ext
    have hxK : (F.θ x : G) ∈ minimalLocalFailureProperPairHull H z beta t := by
      rw [← F.subline]
      exact ⟨x, hx, rfl⟩
    rw [hcu, huK _ hxK, mul_inv_cancel_right]
  have hσ1 : σ ≠ 1 := by
    obtain ⟨x, hxL, hux⟩ := hnontriv
    intro h1
    apply hux
    have h := hσθ (F.θ.symm ⟨x, hxL⟩)
    rw [h1, MulAut.one_apply, MulEquiv.apply_symm_apply] at h
    have h' := congrArg Subtype.val h
    rw [hcu] at h'
    change x = u * x * u⁻¹ at h'
    calc u * x = u * x * u⁻¹ * u := by group
      _ = x * u := by rw [← h']
  have hσ2 : σ ^ 2 = 1 := by
    refine MulEquiv.ext fun x => F.θ.injective ?_
    rw [pow_two, MulAut.mul_apply, hσθ, hσθ, hcu2, MulAut.one_apply]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinv⟩ :=
    unitary_central_cover_subline_automorphism_two_part F.J F.f F.hf F.hcard F.hfixed F.hJ F.C
      F.hC
  obtain ⟨e, he, -, -, -⟩ := hinv σ hσfix hσ1 hσ2
  have hσΨ : ∀ x, σ (sublineAutHom F.J F.C F.hJ F.hC (SemidirectProduct.inl e) x) =
      sublineAutHom F.J F.C F.hJ F.hC (SemidirectProduct.inl e)
        (sublineAutHom F.J F.C F.hJ F.hC
          (SemidirectProduct.inr ⟨F.J.conj, Subgroup.mem_zpowers _⟩) x) := by
    intro x
    rw [← he, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  refine ⟨(normScaleCoord e⁻¹).trans F.rootEquiv, fun w => ?_, fun w => ?_⟩
  ·
    change F.rootHom (normScaleCoord e⁻¹ w) ∈ minimalLocalFailurePairActionPointHull H z ↔ _
    have hQeq : ∀ g, g ∈ minimalLocalFailurePairActionPointHull H z ↔
        g ∈ (upperRootL F.J F.C F.hJ).map (L.subtype.comp F.θ.toMonoidHom) := fun g => by
      rw [F.upper]
    rw [hQeq, UnitaryHullFrame.rootHom, MonoidHom.comp_apply,
      Subgroup.mem_map_iff_mem F.map_injective, mem_upperRootL_iff]
    have he0 : (((e⁻¹ : normOne F.J) : F.kˣ) : F.k) ≠ 0 := Units.ne_zero _
    constructor
    · rintro ⟨w', hw', hww'⟩
      have hw := heisL_injective F.hJ F.hC hww'
      rw [hw, fst_normScaleCoord] at hw'
      exact (mul_eq_zero.mp hw').resolve_left he0
    · intro hw
      exact ⟨_, by rw [fst_normScaleCoord, hw, mul_zero], rfl⟩
  ·
    change u * F.rootHom (normScaleCoord e⁻¹ w) * u⁻¹ =
      F.rootHom (normScaleCoord e⁻¹ (rootTau F.J w))
    rw [UnitaryHullFrame.rootHom_apply, UnitaryHullFrame.rootHom_apply,
      ← sublineAutHom_inl_heisL F.hJ F.hC e w, ← sublineAutHom_inl_heisL F.hJ F.hC e,
      ← sublineAutHom_bar_heisL F.hf F.hcard F.hfixed F.hJ F.hC w, ← hσΨ, hσθ, hcu]

end CFSG.ShultStronglyClosedTI.UnitaryHulls

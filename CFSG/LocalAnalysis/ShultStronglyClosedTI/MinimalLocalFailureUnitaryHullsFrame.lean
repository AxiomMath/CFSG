module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsModelAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFchapter1section1
open scoped LinearAlgebra.Projectivization

variable {G : Type} [Group G]

theorem mem_rightConjugate_iff_conj (A : Subgroup G) (g x : G) :
    x ∈ rightConjugate A g ↔ g * x * g⁻¹ ∈ A := by
  change x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]

structure UnitaryHullFrame (H : Subgroup G) (t : G) (L : Subgroup G) (q : ℕ) : Type 1 where
  k : Type
  [instField : Field k]
  [instFinite : Finite k]
  [instCharP : CharP k 2]
  J : HermitianForm 3 k
  hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  f : ℕ
  hf : 2 ≤ f
  hq : q = 2 ^ f
  hcard : Nat.card k = (2 ^ f) ^ 2
  hfixed : Nat.card {x : k // J.conj x = x} = 2 ^ f
  C : Subgroup J.specialSubgroup
  [instNormal : C.Normal]
  hC : C ≤ scalarCenter J
  θ : J.specialSubgroup ⧸ C ≃* L
  mem_point : ∀ x, ((θ x : L) : G) ∈ H ↔
    coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := k) 0 = unitaryCoordinatePoint 0
  flip : ∀ x, ((θ x : L) : G) = t →
    coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := k) 0 = unitaryCoordinatePoint 2

attribute [instance] UnitaryHullFrame.instField UnitaryHullFrame.instFinite
  UnitaryHullFrame.instCharP UnitaryHullFrame.instNormal

namespace UnitaryHullFrame

variable {H L : Subgroup G} {t : G} {q : ℕ} (F : UnitaryHullFrame H t L q)

theorem coset_eq_iff (x y : F.J.specialSubgroup ⧸ F.C) :
    rightCosetMk H (F.θ x : G) = rightCosetMk H (F.θ y : G) ↔
      coverToPGL F.J F.C F.hJ F.hC x⁻¹ • unitaryCoordinatePoint (K := F.k) 0 =
        coverToPGL F.J F.C F.hJ F.hC y⁻¹ • unitaryCoordinatePoint (K := F.k) 0 := by
  rw [rightCosetMk_eq_iff, show (F.θ y : G) * (F.θ x : G)⁻¹ = (F.θ (y * x⁻¹) : G) by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv], F.mem_point, map_mul, mul_smul,
    map_inv (coverToPGL F.J F.C F.hJ F.hC) y, smul_eq_iff_eq_inv_smul, map_inv]

theorem coset_eq_base_iff (x : F.J.specialSubgroup ⧸ F.C) :
    rightCosetMk H (F.θ x : G) = rightCosetMk H 1 ↔
      coverToPGL F.J F.C F.hJ F.hC x⁻¹ • unitaryCoordinatePoint (K := F.k) 0 =
        unitaryCoordinatePoint 0 := by
  rw [show rightCosetMk H 1 = rightCosetMk H (F.θ 1 : G) by rw [map_one]; rfl, F.coset_eq_iff,
    inv_one, map_one, one_smul]

@[expose] def flipElt (htL : t ∈ L) : F.J.specialSubgroup ⧸ F.C :=
  F.θ.symm ⟨t, htL⟩

theorem θ_flipElt (htL : t ∈ L) : (F.θ (F.flipElt htL) : G) = t := by
  rw [flipElt, MulEquiv.apply_symm_apply]

theorem flipElt_smul (htL : t ∈ L) :
    coverToPGL F.J F.C F.hJ F.hC (F.flipElt htL) • unitaryCoordinatePoint (K := F.k) 0 =
      unitaryCoordinatePoint 2 :=
  F.flip _ (F.θ_flipElt htL)

theorem flipElt_inv (htL : t ∈ L) (ht2 : t * t = 1) : (F.flipElt htL)⁻¹ = F.flipElt htL := by
  rw [inv_eq_iff_mul_eq_one]
  apply F.θ.injective
  apply Subtype.ext
  rw [map_mul, map_one, Subgroup.coe_mul, θ_flipElt, Subgroup.coe_one, ht2]

theorem mem_rightConjugate_iff (htL : t ∈ L) (ht2 : t * t = 1) (x : F.J.specialSubgroup ⧸ F.C) :
    (F.θ x : G) ∈ rightConjugate H t ↔
      coverToPGL F.J F.C F.hJ F.hC x • unitaryCoordinatePoint (K := F.k) 2 =
        unitaryCoordinatePoint 2 := by
  set τ := F.flipElt htL
  have hτ : coverToPGL F.J F.C F.hJ F.hC τ⁻¹ • unitaryCoordinatePoint (K := F.k) 0 =
      unitaryCoordinatePoint 2 := by
    rw [F.flipElt_inv htL ht2]
    exact F.flipElt_smul htL
  rw [mem_rightConjugate_iff_conj,
    show t * (F.θ x : G) * t⁻¹ = (F.θ (τ * x * τ⁻¹) : G) by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        F.θ_flipElt htL],
    F.mem_point, map_mul, map_mul, mul_smul, mul_smul, hτ, smul_eq_iff_eq_inv_smul, ← map_inv,
    hτ]

theorem coset_eq_flip_iff (htL : t ∈ L) (ht2 : t * t = 1) (x : F.J.specialSubgroup ⧸ F.C) :
    rightCosetMk H (F.θ x : G) = rightCosetMk H t ↔
      coverToPGL F.J F.C F.hJ F.hC x⁻¹ • unitaryCoordinatePoint (K := F.k) 0 =
        unitaryCoordinatePoint 2 := by
  have h := F.coset_eq_iff x (F.flipElt htL)
  rwa [F.θ_flipElt htL, F.flipElt_inv htL ht2, F.flipElt_smul htL] at h

theorem mem_pairPointStabilizer_iff (htL : t ∈ L) (ht2 : t * t = 1)
    {beta : rightCosetSpace H} (hbeta : beta = rightCosetMk H t) (x : F.J.specialSubgroup ⧸ F.C) :
    (F.θ x : G) ∈ pairPointStabilizer H beta ↔ x ∈ pairStabilizerL F.J F.C F.hJ F.hC := by
  rw [pairPointStabilizer, hbeta, rightCosetStabilizer_base, rightCosetStabilizer_mk,
    Subgroup.mem_inf, F.mem_point, F.mem_rightConjugate_iff htL ht2]
  rfl

@[expose] def rootHom : hermitianUnipotentCoord F.J →* G :=
  (L.subtype.comp F.θ.toMonoidHom).comp (heisL F.J F.C F.hJ)

theorem rootHom_apply (z : hermitianUnipotentCoord F.J) :
    F.rootHom z = (F.θ (heisL F.J F.C F.hJ z) : G) :=
  rfl

theorem rootHom_injective : Function.Injective F.rootHom := fun _ _ h =>
  heisL_injective F.hJ F.hC (F.θ.injective (Subtype.ext h))

@[expose] def root : Subgroup G :=
  F.rootHom.range

@[expose] def rootEquiv : hermitianUnipotentCoord F.J ≃* F.root :=
  MonoidHom.ofInjective F.rootHom_injective

theorem coe_rootEquiv (z : hermitianUnipotentCoord F.J) :
    (F.rootEquiv z : G) = F.rootHom z :=
  rfl

theorem root_le_point : F.root ≤ H := by
  rintro _ ⟨z, rfl⟩
  exact (F.mem_point _).mpr (heisL_smul_zero F.hJ F.hC z)

theorem root_le : F.root ≤ L := by
  rintro _ ⟨z, rfl⟩
  exact (F.θ (heisL F.J F.C F.hJ z)).2

theorem root_regular (x y : F.J.specialSubgroup ⧸ F.C)
    (hx : rightCosetMk H (F.θ x : G) ≠ rightCosetMk H 1)
    (hy : rightCosetMk H (F.θ y : G) ≠ rightCosetMk H 1) :
    ∃! z : hermitianUnipotentCoord F.J,
      rightCosetTranslate H (rightCosetMk H (F.θ x : G)) (F.rootHom z) =
        rightCosetMk H (F.θ y : G) := by
  have key : ∀ z : hermitianUnipotentCoord F.J,
      rightCosetTranslate H (rightCosetMk H (F.θ x : G)) (F.rootHom z) =
          rightCosetMk H (F.θ y : G) ↔
        coverToPGL F.J F.C F.hJ F.hC (heisL F.J F.C F.hJ z⁻¹) •
            (coverToPGL F.J F.C F.hJ F.hC x⁻¹ • unitaryCoordinatePoint (K := F.k) 0) =
          coverToPGL F.J F.C F.hJ F.hC y⁻¹ • unitaryCoordinatePoint (K := F.k) 0 := by
    intro z
    rw [rightCosetTranslate_mk, rootHom_apply, show (F.θ x : G) * (F.θ (heisL F.J F.C F.hJ z) : G) =
      (F.θ (x * heisL F.J F.C F.hJ z) : G) by rw [map_mul, Subgroup.coe_mul], F.coset_eq_iff,
      _root_.mul_inv_rev, map_mul, mul_smul, map_inv (heisL F.J F.C F.hJ) z]
  rw [ne_eq, F.coset_eq_base_iff] at hx hy
  obtain ⟨w, hw, huniq⟩ := heisL_regular F.hf F.hcard F.hfixed F.hJ F.hC hx hy
  refine ⟨w⁻¹, (key _).mpr (by rwa [inv_inv]), fun z hz => ?_⟩
  rw [← huniq z⁻¹ ((key z).mp hz), inv_inv]

end UnitaryHullFrame

end CFSG.ShultStronglyClosedTI.UnitaryHulls

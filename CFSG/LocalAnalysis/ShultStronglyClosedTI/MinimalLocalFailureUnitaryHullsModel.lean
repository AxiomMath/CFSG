module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {J : HermitianForm 3 K} {C : Subgroup J.specialSubgroup} [C.Normal]

variable (J C) in
@[expose] def heisL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    hermitianUnipotentCoord J →* J.specialSubgroup ⧸ C :=
  (QuotientGroup.mk' C).comp (hermitianUnipotentSU J hJ)

theorem coe_hermitianUnipotentSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J) :
    (((hermitianUnipotentSU J hJ z : J.specialSubgroup) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![1, z.1.1, z.1.2; 0, 1, -J.conj z.1.1; 0, 0, 1] :=
  rfl

theorem coverToPGL_heisL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (z : hermitianUnipotentCoord J) :
    coverToPGL J C hJ hC (heisL J C hJ z) = ProjGenLinGroup.mk (hermitianUnipotentGL J z) :=
  rfl

theorem heisL_injective (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) : Function.Injective (heisL J C hJ) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hmem : hermitianUnipotentSU J hJ z ∈ C := (QuotientGroup.eq_one_iff _).mp hz
  obtain ⟨c, hc, -, -⟩ := hC hmem
  rw [coe_hermitianUnipotentSU] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e02 := congrFun (congrFun hc 0) 2
  simp [scalar_apply] at e00 e01 e02
  exact coord_ext' e01 e02
where
  coord_ext' {z : hermitianUnipotentCoord J} (h1 : z.1.1 = 0) (h2 : z.1.2 = 0) : z = 1 :=
    Subtype.ext (Prod.ext h1 h2)

theorem heisL_smul_zero (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (z : hermitianUnipotentCoord J) :
    coverToPGL J C hJ hC (heisL J C hJ z) • unitaryCoordinatePoint (K := K) 0 =
      unitaryCoordinatePoint 0 := by
  rw [coverToPGL_heisL, unitary_projective_coordinate_maps_iff]
  intro k hk
  fin_cases k
  · exact (hk rfl).elim
  · simp [hermitianUnipotentGL_val, hermitianUnipotentMatrix]
  · simp [hermitianUnipotentGL_val, hermitianUnipotentMatrix]

theorem hermitianUnipotentGL_mk_injective {z w : hermitianUnipotentCoord J}
    (h : ProjGenLinGroup.mk (hermitianUnipotentGL J z) =
      ProjGenLinGroup.mk (hermitianUnipotentGL J w)) : z = w := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hu' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hu
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hermitianUnipotentGL_val,
    hermitianUnipotentMatrix_eq] at hu'
  have e00 := congrFun (congrFun hu' 0) 0
  have e01 := congrFun (congrFun hu' 0) 1
  have e02 := congrFun (congrFun hu' 0) 2
  simp [Matrix.mul_apply, scalar_apply, diagonal_apply] at e00 e01 e02
  rw [e00, Units.val_one, mul_one] at e01 e02
  exact Subtype.ext (Prod.ext e01 e02)

section CharTwo

variable [CharP K 2]

@[expose] def heisCenterCoord (b : unitaryCoverFixedField J) : hermitianUnipotentCoord J :=
  ⟨(0, (b : K)), by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hb : J.conj (b : K) = b := b.2
    simp only [hb, zero_mul, add_zero]
    linear_combination (b : K) * h2⟩

theorem heisL_heisCenterCoord (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (b : unitaryCoverFixedField J) :
    heisL J C hJ (heisCenterCoord b) =
      (QuotientGroup.mk' C) (sublineHom J hJ (upperSL _ (Multiplicative.ofAdd b))) := by
  change ((hermitianUnipotentSU J hJ (heisCenterCoord b) : J.specialSubgroup) :
    J.specialSubgroup ⧸ C) = ((sublineHom J hJ (upperSL _ (Multiplicative.ofAdd b)) :
      J.specialSubgroup) : J.specialSubgroup ⧸ C)
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_hermitianUnipotentSU, coe_sublineHom_upperSL]
  simp [heisCenterCoord]

theorem mem_upperRootL_iff (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (x : J.specialSubgroup ⧸ C) :
    x ∈ upperRootL J C hJ ↔ ∃ z : hermitianUnipotentCoord J, z.1.1 = 0 ∧ heisL J C hJ z = x := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨heisCenterCoord (Multiplicative.toAdd b), rfl, heisL_heisCenterCoord hJ _⟩
  · rintro ⟨z, hz, rfl⟩
    have hb : J.conj z.1.2 = z.1.2 := by
      have h := z.2
      rw [hz, zero_mul, add_zero] at h
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h - z.1.2 * h2
    refine ⟨Multiplicative.ofAdd ⟨z.1.2, hb⟩, ?_⟩
    change (QuotientGroup.mk' C) (sublineHom J hJ (upperSL _ (Multiplicative.ofAdd ⟨z.1.2, hb⟩))) =
      heisL J C hJ z
    rw [← heisL_heisCenterCoord hJ]
    congr 1
    exact Subtype.ext (Prod.ext hz.symm rfl)

theorem upperRootL_smul_zero (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) {x : J.specialSubgroup ⧸ C} (hx : x ∈ upperRootL J C hJ) :
    coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint 0 := by
  obtain ⟨z, -, rfl⟩ := (mem_upperRootL_iff hJ x).mp hx
  exact heisL_smul_zero hJ hC z

theorem lowerRootL_smul_two (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) {x : J.specialSubgroup ⧸ C} (hx : x ∈ lowerRootL J C hJ) :
    coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := K) 2 = unitaryCoordinatePoint 2 := by
  obtain ⟨b, rfl⟩ := hx
  change ProjGenLinGroup.mk ((sublineHom J hJ (lowerSL _ b) : J.specialSubgroup) :
    GL (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 = _
  rw [unitary_projective_coordinate_maps_iff]
  intro k hk
  rw [coe_sublineHom_lowerSL]
  fin_cases k
  · simp
  · simp
  · exact (hk rfl).elim

theorem upperRootL_mul_self (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {x : J.specialSubgroup ⧸ C} (hx : x ∈ upperRootL J C hJ) : x * x = 1 := by
  obtain ⟨b, rfl⟩ := hx
  rw [← map_mul]
  convert map_one ((QuotientGroup.mk' C).comp ((sublineHom J hJ).comp (upperSL _))) using 2
  change Multiplicative.ofAdd (Multiplicative.toAdd b + Multiplicative.toAdd b) = 1
  rw [CharTwo.add_self_eq_zero, ofAdd_zero]

theorem lowerRootL_mul_self (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {x : J.specialSubgroup ⧸ C} (hx : x ∈ lowerRootL J C hJ) : x * x = 1 := by
  obtain ⟨b, rfl⟩ := hx
  rw [← map_mul]
  convert map_one ((QuotientGroup.mk' C).comp ((sublineHom J hJ).comp (lowerSL _))) using 2
  change Multiplicative.ofAdd (Multiplicative.toAdd b + Multiplicative.toAdd b) = 1
  rw [CharTwo.add_self_eq_zero, ofAdd_zero]

theorem card_lowerRootL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    Nat.card (lowerRootL J C hJ) = Nat.card (unitaryCoverFixedField J) := by
  have hinj : Function.Injective
      ((QuotientGroup.mk' C).comp
        ((sublineHom J hJ).comp (lowerSL (unitaryCoverFixedField J)))) := by
    intro s t hst
    have h1 := sublineL_injective hJ hC hst
    have h2 := congrArg (fun x : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) =>
      (x : Matrix (Fin 2) (Fin 2) (unitaryCoverFixedField J)) 1 0) h1
    simp only [coe_lowerSL] at h2
    simpa using h2
  rw [lowerRootL, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

end CharTwo

end CFSG.ShultStronglyClosedTI.UnitaryHulls

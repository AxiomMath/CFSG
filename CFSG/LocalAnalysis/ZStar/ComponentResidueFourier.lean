module

public import CFSG.LocalAnalysis.ZStar.RegularBrauerQuotient
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockFourierStability

public section

namespace CFSG

namespace ZStar.ComponentResidueFourier

open ZStar.ComponentIntegralLattice
open ZStar.Helpers
open ZStar.ModularBrauerQuotient
open ZStar.OddRootResidue
open ZStar.PadicBlockField
open ZStar.PadicBlockLift
open ZStar.PrincipalBlockFourierStability
open ZStar.PrincipalBlockKernel
open ZStar.RegularBrauerQuotient
open ZStar.TwoAdicWedderburn
open ZStar.WedderburnBlock

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

attribute [local instance 2000] CommRing.toCommSemiring

@[expose] def componentResidueRepresentation
    (D : Decomposition G) (i : Fin D.blockCount) :
    Representation Residue2 G
      (Fin (D.blockSize i) → Residue2) where
  toFun g := Matrix.toLin'
    ((componentIntegralMatrix D i g).map
      (IsLocalRing.residue OddRootResidue.O2))
  map_one' := by
    rw [componentIntegralMatrix_one]
    apply LinearMap.ext
    intro x
    ext j
    simp
  map_mul' g h := by
    rw [componentIntegralMatrix_mul, Matrix.map_mul, Matrix.toLin'_mul]
    exact (Module.End.mul_eq_comp _ _).symm

@[simp]
theorem componentResidueRepresentation_apply
    (D : Decomposition G) (i : Fin D.blockCount) (g : G) :
    componentResidueRepresentation D i g =
      Matrix.toLin'
        ((componentIntegralMatrix D i g).map
          (IsLocalRing.residue OddRootResidue.O2)) :=
  rfl

noncomputable local instance residue2AlgebraZModTwo :
    Algebra (ZMod 2) Residue2 :=
  OddRootResidue.zmod2ToResidue.toAlgebra

@[expose] def componentResidueRepresentationZMod
    (D : Decomposition G) (i : Fin D.blockCount) :
    Representation (ZMod 2) G
      (Fin (D.blockSize i) → Residue2) where
  toFun g := LinearMap.restrictScalars (ZMod 2)
    (componentResidueRepresentation D i g)
  map_one' := by
    apply LinearMap.ext
    intro x
    change componentResidueRepresentation D i 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change componentResidueRepresentation D i (g * h) x =
      componentResidueRepresentation D i g
        (componentResidueRepresentation D i h x)
    rw [map_mul]
    rfl

@[simp]
theorem componentResidueRepresentationZMod_apply
    (D : Decomposition G) (i : Fin D.blockCount) (g : G) :
    componentResidueRepresentationZMod D i g =
      LinearMap.restrictScalars (ZMod 2)
        (Matrix.toLin'
          ((componentIntegralMatrix D i g).map
            (IsLocalRing.residue OddRootResidue.O2))) :=
  rfl

@[simp]
theorem componentResidueRepresentationZMod_apply_vector
    (D : Decomposition G) (i : Fin D.blockCount) (g : G)
    (x : Fin (D.blockSize i) → Residue2) :
    componentResidueRepresentationZMod D i g x =
      Matrix.toLin'
        ((componentIntegralMatrix D i g).map
          (IsLocalRing.residue OddRootResidue.O2)) x :=
  rfl

theorem involutionDifference_componentResidueRepresentationZMod_apply
    (D : Decomposition G) (i : Fin D.blockCount) (w : G)
    (x : Fin (D.blockSize i) → Residue2) :
    involutionDifference (componentResidueRepresentationZMod D i) w x =
      Matrix.toLin'
        ((componentIntegralMatrix D i w).map
          (IsLocalRing.residue OddRootResidue.O2) - 1) x := by
  change Matrix.toLin'
      ((componentIntegralMatrix D i w).map
        (IsLocalRing.residue OddRootResidue.O2)) x - x = _
  rw [map_sub, Matrix.toLin'_one, LinearMap.sub_apply]
  rfl

private theorem representation_asAlgebraHom_eq_sum'
    {k : Type*} [CommSemiring k]
    {X : Type*} [Group X] [Fintype X]
    {W : Type*} [AddCommMonoid W] [Module k W]
    (rho : Representation k X W) (a : MonoidAlgebra k X) :
    rho.asAlgebraHom a = ∑ g : X, a.coeff g • rho g := by
  classical
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  apply Finsupp.sum_fintype
  intro g
  exact zero_smul k (rho g)

private theorem componentResidueRepresentationZMod_asAlgebraHom
    (D : Decomposition G) (i : Fin D.blockCount)
    (a : GroupAlgebraTwo G) :
    (componentResidueRepresentationZMod D i).asAlgebraHom a =
      LinearMap.restrictScalars (ZMod 2)
        ((componentResidueRepresentation D i).asAlgebraHom
          (MonoidAlgebra.mapRingHom G OddRootResidue.zmod2ToResidue a)) := by
  rw [representation_asAlgebraHom_eq_sum',
    representation_asAlgebraHom_eq_sum']
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.restrictScalars_apply, MonoidAlgebra.coeff_mapRingHom,
    componentResidueRepresentationZMod_apply]
  apply Finset.sum_congr rfl
  intro g hg
  rfl

private def componentIntegralAlgebraMatrix
    (D : Decomposition G) (i : Fin D.blockCount)
    (a : MonoidAlgebra OddRootResidue.O2 G) :
    Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i))
      OddRootResidue.O2 :=
  ∑ g : G, a.coeff g • componentIntegralMatrix D i g

private theorem componentIntegralAlgebraMatrix_eq_toMatrix
    (D : Decomposition G) (i : Fin D.blockCount)
    (a : MonoidAlgebra OddRootResidue.O2 G) :
    componentIntegralAlgebraMatrix D i a =
      LinearMap.toMatrix (componentIntegralBasis D i)
        (componentIntegralBasis D i)
        ((componentIntegralRepresentation D i).asAlgebraHom a) := by
  rw [representation_asAlgebraHom_eq_sum']
  apply Matrix.ext
  intro j k
  simp [componentIntegralAlgebraMatrix,
    componentIntegralRepresentation_toMatrix]

private theorem componentResidueRepresentation_asAlgebraHom_map_residue
    (D : Decomposition G) (i : Fin D.blockCount)
    (a : MonoidAlgebra OddRootResidue.O2 G) :
    (componentResidueRepresentation D i).asAlgebraHom
        (MonoidAlgebra.mapRingHom G
          (IsLocalRing.residue OddRootResidue.O2) a) =
      Matrix.toLin'
        ((componentIntegralAlgebraMatrix D i a).map
          (IsLocalRing.residue OddRootResidue.O2)) := by
  have hmap :
      (componentIntegralAlgebraMatrix D i a).map
          (IsLocalRing.residue OddRootResidue.O2) =
        ∑ g : G,
          (IsLocalRing.residue OddRootResidue.O2) (a.coeff g) •
            (componentIntegralMatrix D i g).map
              (IsLocalRing.residue OddRootResidue.O2) := by
    apply Matrix.ext
    intro j k
    simp only [componentIntegralAlgebraMatrix, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.map_apply, map_sum, map_mul, smul_eq_mul]
  rw [representation_asAlgebraHom_eq_sum']
  apply LinearMap.ext
  intro x
  ext j
  rw [hmap]
  simp [Matrix.toLin'_apply]

private theorem selected_componentIntegralAlgebraMatrix_principalBlockO2
    (D : Decomposition G) (i : Fin D.blockCount)
    (hi : i ∈ selectedIndices D.equiv
      (principalBlockTwoAdic (G := G))) :
    componentIntegralAlgebraMatrix D i (principalBlockO2 (G := G)) = 1 := by
  rw [componentIntegralAlgebraMatrix_eq_toMatrix,
    componentIntegralRepresentation_principalBlockO2 D i hi,
    LinearMap.toMatrix_one]

private theorem selected_componentResidueRepresentation_principalBlockResidue
    (D : Decomposition G) (i : Fin D.blockCount)
    (hi : i ∈ selectedIndices D.equiv
      (principalBlockTwoAdic (G := G))) :
    (componentResidueRepresentation D i).asAlgebraHom
        (MonoidAlgebra.mapRingHom G OddRootResidue.zmod2ToResidue
          (principalBlockCandidate G)) = 1 := by
  rw [← principalBlockO2_map_residue,
    componentResidueRepresentation_asAlgebraHom_map_residue,
    selected_componentIntegralAlgebraMatrix_principalBlockO2 D i hi]
  apply LinearMap.ext
  intro x
  ext j
  simp

theorem selected_componentResidueRepresentation_principalBlockActsAsIdentity
    (D : Decomposition G) (i : Fin D.blockCount)
    (hi : i ∈ selectedIndices D.equiv
      (principalBlockTwoAdic (G := G))) :
    PrincipalBlockActsAsIdentity
      (componentResidueRepresentationZMod D i) := by
  change (componentResidueRepresentationZMod D i).asAlgebraHom
      (principalBlockCandidate G) = 1
  rw [componentResidueRepresentationZMod_asAlgebraHom,
    selected_componentResidueRepresentation_principalBlockResidue D i hi]
  apply LinearMap.ext
  intro x
  rfl

end

end ZStar.ComponentResidueFourier

end CFSG

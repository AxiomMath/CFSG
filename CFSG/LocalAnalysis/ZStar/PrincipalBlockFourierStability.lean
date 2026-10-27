module

public import CFSG.LocalAnalysis.ZStar.ComponentIntegralLattice
public import CFSG.LocalAnalysis.ZStar.OddFourierProjectors
public import CFSG.LocalAnalysis.ZStar.OddRootResidue
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockCharacterStability
public import CFSG.LocalAnalysis.ZStar.ModularBrauerQuotient

public section

namespace CFSG

namespace ZStar.PrincipalBlockFourierStability

open ZStar.AbstractStepV
open ZStar.BrauerPrincipal
open ZStar.ComponentIntegralLattice
open ZStar.Helpers
open ZStar.ModularBrauerQuotient
open ZStar.OddFourierProjectors
open ZStar.OddRootResidue
open ZStar.PadicBlockField
open ZStar.PadicBlockLift
open ZStar.PadicBlockProperties
open ZStar.PrincipalBlockCharacterStability
open ZStar.PrincipalBlockKernel
open ZStar.TwoAdicWedderburn
open ZStar.WedderburnBlock

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

attribute [local instance 2000] CommRing.toCommSemiring

noncomputable def principalBlockO2 :
    MonoidAlgebra OddRootResidue.O2 G :=
  MonoidAlgebra.mapRingHom G OddRootResidue.padicIntToO2
    (principalBlockPadic (G := G))

private theorem principalBlockO2_map_algebraMap :
    MonoidAlgebra.mapRingHom G
        (algebraMap OddRootResidue.O2 TwoAdicComplex)
        (principalBlockO2 (G := G)) =
      principalBlockTwoAdic (G := G) := by
  ext g
  simp [principalBlockO2, principalBlockTwoAdic]

theorem principalBlockO2_map_residue :
    MonoidAlgebra.mapRingHom G
        (IsLocalRing.residue OddRootResidue.O2)
        (principalBlockO2 (G := G)) =
      MonoidAlgebra.mapRingHom G OddRootResidue.zmod2ToResidue
        (principalBlockCandidate G) := by
  ext g
  simp only [principalBlockO2, MonoidAlgebra.coeff_mapRingHom,
    OddRootResidue.residue_padicIntToO2]
  congr 1
  rw [← OddRootResidue.toZModPow_one_eq_toZMod]
  exact toZModPow_one_principalBlockPadic_coeff g

private theorem componentRepresentation_asAlgebraHom_eq
    (D : Decomposition G) (i : Fin D.blockCount)
    (a : MonoidAlgebra TwoAdicComplex G) :
    (componentRepresentation D i).asAlgebraHom a =
      Matrix.toLinAlgEquiv' (D.equiv a i) := by
  apply DFunLike.congr_fun (f := (componentRepresentation D i).asAlgebraHom)
      (g := Matrix.toLinAlgEquiv'.toAlgHom.comp (componentAlgHom D i))
      ?_ a
  apply MonoidAlgebra.algHom_ext
  · intro g
    rw [Representation.asAlgebraHom_single_one]
    exact componentRepresentation_apply D i g
  · ext

private theorem componentIntegral_asAlgebraHom_coe
    (D : Decomposition G) (i : Fin D.blockCount)
    (a : MonoidAlgebra OddRootResidue.O2 G)
    (x : componentOrbitLattice D i) :
    ((((componentIntegralRepresentation D i).asAlgebraHom a) x :
        componentOrbitLattice D i) :
      Fin (D.blockSize i) → TwoAdicComplex) =
      (componentRepresentation D i).asAlgebraHom
        (MonoidAlgebra.mapRingHom G
          (algebraMap OddRootResidue.O2 TwoAdicComplex) a) x := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
      simpa [Representation.asAlgebraHom_of] using
        componentIntegralRepresentation_apply D i g x
  | add a b ha hb =>
      simpa only [map_add, LinearMap.add_apply, Submodule.coe_add,
        Pi.add_apply] using congrArg₂ (· + ·) ha hb
  | smul r a ha =>
      have hmap :
          MonoidAlgebra.mapRingHom G
              (algebraMap OddRootResidue.O2 TwoAdicComplex) (r • a) =
            (algebraMap OddRootResidue.O2 TwoAdicComplex r) •
              MonoidAlgebra.mapRingHom G
                (algebraMap OddRootResidue.O2 TwoAdicComplex) a := by
        ext g
        simp
      rw [map_smul, LinearMap.smul_apply, hmap, map_smul,
        LinearMap.smul_apply]
      change (algebraMap OddRootResidue.O2 TwoAdicComplex r) •
          ((((componentIntegralRepresentation D i).asAlgebraHom a) x :
            componentOrbitLattice D i) :
            Fin (D.blockSize i) → TwoAdicComplex) =
        (algebraMap OddRootResidue.O2 TwoAdicComplex r) •
          ((componentRepresentation D i).asAlgebraHom
            (MonoidAlgebra.mapRingHom G
              (algebraMap OddRootResidue.O2 TwoAdicComplex) a) x)
      exact congrArg
        ((algebraMap OddRootResidue.O2 TwoAdicComplex r) • ·) ha

private theorem componentRepresentation_principalBlockTwoAdic
    (D : Decomposition G) (i : Fin D.blockCount)
    (hi : i ∈ selectedIndices D.equiv
      (principalBlockTwoAdic (G := G))) :
    (componentRepresentation D i).asAlgebraHom
        (principalBlockTwoAdic (G := G)) = 1 := by
  have hi' := mem_selectedIndices.mp hi
  rw [componentRepresentation_asAlgebraHom_eq]
  rw [hi', map_one]

theorem componentIntegralRepresentation_principalBlockO2
    (D : Decomposition G) (i : Fin D.blockCount)
    (hi : i ∈ selectedIndices D.equiv
      (principalBlockTwoAdic (G := G))) :
    (componentIntegralRepresentation D i).asAlgebraHom
        (principalBlockO2 (G := G)) = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((((componentIntegralRepresentation D i).asAlgebraHom
      (principalBlockO2 (G := G))) x : componentOrbitLattice D i) :
        Fin (D.blockSize i) → TwoAdicComplex) = x
  rw [componentIntegral_asAlgebraHom_coe,
    principalBlockO2_map_algebraMap]
  have h := congrArg
    (fun f : Module.End TwoAdicComplex
        (Fin (D.blockSize i) → TwoAdicComplex) ↦ f x)
    (componentRepresentation_principalBlockTwoAdic D i hi)
  simpa using h

end

end ZStar.PrincipalBlockFourierStability

end CFSG

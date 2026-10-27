module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts1
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3NormalFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3MatrixCoreAA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3MatrixCoreAA2
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Subgroup
  CFSG.Open

theorem s16h_e3_z3_transvection_normal_five
    (N K : Subgroup (coordinateSemilinearGroup 3 OmegaField))
    (hKN : K ≤ N) (hKnorm : (K.subgroupOf N).Normal)
    (hO2 : ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField), P ≤ K →
      (P.subgroupOf K).Normal → IsPGroup 2 P → P = ⊥)
    (hZK : ∀ c : OmegaFieldˣ, (SemidirectProduct.inl
      (Matrix.GeneralLinearGroup.scalar (Fin 3) c) : coordinateSemilinearGroup 3 OmegaField) ∈ K)
    (hno : ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField), P ≤ K →
      IsElemAbelian 3 P → Nat.card ↥P < 9)
    {u : Matrix.GeneralLinearGroup (Fin 3) OmegaField}
    (huK : (SemidirectProduct.inl u : coordinateSemilinearGroup 3 OmegaField) ∈ K)
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ F : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField),
      Nat.card ↥F = 5 ∧
      ((Subgroup.map (SemidirectProduct.inl :
        Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
          coordinateSemilinearGroup 3 OmegaField) F).subgroupOf N).Normal ∧
      Subgroup.map (SemidirectProduct.inl :
        Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
          coordinateSemilinearGroup 3 OmegaField) F ≤ K := by
  haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  haveI : Finite OmegaField := Module.finite_of_finite (ZMod 2)
  haveI : Finite (OmegaField ≃+* OmegaField) :=
    Finite.of_injective (fun σ : OmegaField ≃+* OmegaField => (σ : OmegaField → OmegaField))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  haveI : Finite (coordinateSemilinearGroup 3 OmegaField) :=
    Finite.of_injective (fun g : coordinateSemilinearGroup 3 OmegaField => (g.left, g.right))
      (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  obtain ⟨D, hDK, hDN, hDrange, hDnt, hgen, hO2D, hcard, h3, h7⟩ :=
    s16h_e3_z3_transvection_closure_hypotheses N K hKN hKnorm hO2 hZK hno huK hu2 hu1
  haveI : Nontrivial ↥D := hDnt
  obtain ⟨F, hFnorm, hFcard⟩ :=
    s16h_e3_exists_normal_card_five (D := ↥D) hgen hO2D hcard h3 h7
  exact s16h_e3_z3_normal_five_of_closure N K D hDK hDN hDrange hcard F hFnorm hFcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

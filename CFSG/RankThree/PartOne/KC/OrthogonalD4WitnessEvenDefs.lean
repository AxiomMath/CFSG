module

public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourDefs

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalD4

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups

section Even

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {E : Type} [Field E] [Algebra K E]

@[expose] noncomputable def hermU (D : EvenNormPlane K E) : hermFourSpace D.σ :=
  hermFourCoord D (((fun _ => 0), (fun _ => 0)), 1)

@[expose] noncomputable def hermI (D : EvenNormPlane K E) : hermFourSpace D.σ :=
  hermFourCoord D (((fun _ => 1), (fun _ => 1)), 0)

theorem coe_hermU (D : EvenNormPlane K E) :
    (hermU D : Matrix (Fin 2) (Fin 2) E) = !![0, 1; 1, 0] := by
  change (hermFourCoordLin D (((fun _ => 0), (fun _ => 0)), 1) : Matrix (Fin 2) (Fin 2) E) = _
  rw [coe_hermFourCoordLin]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermFourMat, map_one]

theorem coe_hermI (D : EvenNormPlane K E) : (hermI D : Matrix (Fin 2) (Fin 2) E) = 1 := by
  change (hermFourCoordLin D (((fun _ => 1), (fun _ => 1)), 0) : Matrix (Fin 2) (Fin 2) E) = _
  rw [coe_hermFourCoordLin]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermFourMat]

theorem det_swap_eq_one [CharP E 2] : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E).det = 1 := by
  rw [Matrix.det_fin_two_of]
  simp [CharTwo.neg_eq]

@[expose] noncomputable def hermSwap (_D : EvenNormPlane K E) : SL(2, E) :=
  ⟨!![0, 1; 1, 0], by
    have : CharP E 2 := charP_two_of_algebra (K := K)
    exact det_swap_eq_one⟩

@[expose] def EvenD4Witness (Q : QuadraticForm K (Fin d → K))
    (a : MulAut (matrixProjectiveDerived Q)) (W : Submodule K (Fin d → K)) : Prop :=
  supportedMatrix Q W ≤ matrixDerived Q ∧
  (∀ B : Subgroup (MulAut (matrixProjectiveDerived Q)),
    CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ B →
      supportedInner Q W ≤
        B ⊓ Subgroup.centralizer ({a} : Set (MulAut (matrixProjectiveDerived Q))) ∧
      CFSG.IsComponent ((supportedInner Q W).subgroupOf
        (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (matrixProjectiveDerived Q)))))) ∧
  (∃ (E : Type) (_ : Field E) (_ : Algebra K E) (D : EvenNormPlane K E)
      (ψ : W ≃ₗ[K] hermFourSpace D.σ),
    (∀ w : W, hermFourForm D (ψ w) = Q (w : Fin d → K)) ∧
    ∀ u v : W, ψ u = hermU D → ψ v = hermI D →
      LinearIndependent K ![(u : Fin d → K), (v : Fin d → K)] ∧ Q u = 1 ∧ Q v = 1 ∧
      polar Q (u : Fin d → K) (v : Fin d → K) = 0 ∧
      ∃ g : matrixDerived Q,
        (matrixLinearEquiv g.val : (Fin d → K) →ₗ[K] (Fin d → K)) =
          orthElementaryMap Q ((u : Fin d → K) + (v : Fin d → K)) (u : Fin d → K) ∧
        g.val ∈ supportedMatrix Q W ∧ g ≠ 1 ∧ g * g = 1 ∧
        (∀ w : W, matrixLinearEquiv g.val (w : Fin d → K) =
          (ψ.symm (hermFourRho D (hermSwap D) (ψ w)) : Fin d → K)) ∧
        (∀ z ∈ orthPerp Q W, matrixLinearEquiv g.val z = z) ∧
        MulAut.conj (matrixProjectiveProjection Q g) ∈ supportedInner Q W ∧
        ∀ α : MulAut (matrixProjectiveDerived Q),
          α ∈ Subgroup.centralizer
            ({MulAut.conj (matrixProjectiveProjection Q g)} :
              Set (MulAut (matrixProjectiveDerived Q))) →
          α ∈ matrixProjectiveImage Q) ∧
  Subgroup.centralizer (supportedInner Q W : Set (MulAut (matrixProjectiveDerived Q))) ≤
    matrixProjectiveImage Q ∧
  ∀ B : Subgroup (MulAut (matrixProjectiveDerived Q)),
    CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ B →
      Subgroup.centralizer (layerCentralizer B a : Set (MulAut (matrixProjectiveDerived Q))) ≤
        matrixProjectiveImage Q

end Even

end CFSG.RankThree.PartOne.KCOrthogonalD4

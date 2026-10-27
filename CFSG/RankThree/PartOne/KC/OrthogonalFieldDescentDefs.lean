module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.Blueprint.SourceClassicalModels
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open TensorProduct Matrix CFSG.GroupTheory.SteinbergBK CFSG.Assembly.LowTwoRank
  CFSG.Blueprint.EvenSource CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.Classical2

variable {K : Type} [Field K] {d : ℕ}

abbrev fixedField (U : coordinateSemilinearGroup d K) : Subfield K :=
  semilinearFixedSubfield U.right

abbrev fixedSpace (U : coordinateSemilinearGroup d K) :
    Submodule (fixedField U) (Fin d → K) :=
  semilinearFixedSubmodule U.right (coordinateSemilinearMap U) (coordinateSemilinearMap_smul U)

theorem mem_fixedSpace {U : coordinateSemilinearGroup d K} {v : Fin d → K} :
    v ∈ fixedSpace U ↔ coordinateSemilinearMap U v = v := Iff.rfl

@[expose] def FixedFormDescent (p : ℕ) (Q : QuadraticForm K (Fin d → K)) (U : similarityPairs Q)
    (c : Kˣ) (Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)) : Prop :=
  U.val ^ p = 1 ∧ (∀ w, ((Q₀ w : fixedField U.val) : K) = c * Q w) ∧
  (QuadraticMap.polarBilin Q₀).Nondegenerate ∧
  (∃ Φ : K ⊗[fixedField U.val] fixedSpace U.val ≃ₗ[K] (Fin d → K),
    (∀ x w, Φ (x ⊗ₜ w) = x • (w : Fin d → K)) ∧
    (∀ x w, coordinateSemilinearMap U.val (Φ (x ⊗ₜ w)) = Φ (U.val.right x ⊗ₜ w)) ∧
    ∀ (x y : K) (w w' : fixedSpace U.val),
      c * Q (Φ (x ⊗ₜ w)) = x ^ 2 * ((Q₀ w : fixedField U.val) : K) ∧
      c * QuadraticMap.polar Q (Φ (x ⊗ₜ w)) (Φ (y ⊗ₜ w')) =
        x * y * ((QuadraticMap.polar Q₀ w w' : fixedField U.val) : K)) ∧
  Module.finrank (fixedField U.val) (fixedSpace U.val) = d ∧
  sourceWittIndex ⇑Q₀ = sourceWittIndex ⇑Q ∧
  ∃ T : Submodule (fixedField U.val) (fixedSpace U.val),
    Module.finrank (fixedField U.val) T = 3 ∧ ∀ x ∈ T, Q₀ x = 0

@[expose] def TransportsToCoordinateField {ι : Type} (e : ι ≃ Fin d)
    (Q Q' : QuadraticForm K (Fin d → K)) (U : similarityPairs Q)
    (S₀ : fixedSpace U.val ≃ₗ[fixedField U.val] (ι → fixedField U.val)) : Prop :=
  ∃ (S : GL (Fin d) K) (ν : Kˣ), (∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) ∧
    (∀ w : fixedSpace U.val, (S : Matrix (Fin d) (Fin d) K) *ᵥ (w : Fin d → K) =
      fun j => ((S₀ w (e.symm j) : fixedField U.val) : K)) ∧
    S * U.val.left = glFieldAut (Fin d) K U.val.right S ∧
    ∃ Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q',
      (∀ A : matrixDerived Q, ∃ B : matrixDerived Q', (B : GL (Fin d) K) = S * A * S⁻¹ ∧
        Θ (matrixProjectiveProjection Q A) = matrixProjectiveProjection Q' B) ∧
      ∃ g : similarityPairs Q', g.val.left = 1 ∧ g.val.right = U.val.right ∧
        ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
          matrixProjectiveConjugationHom Q' g (Θ x)

@[expose] def OddFieldDescent (n ℓ f p : ℕ) (Q : QuadraticForm K (Fin (2 * n + 1) → K))
    (U : similarityPairs Q) (Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)) : Prop :=
  ∃ (ν : (fixedField U.val)ˣ)
    (S₀ : fixedSpace U.val ≃ₗ[fixedField U.val] (Fin n ⊕ Fin n ⊕ Unit → fixedField U.val)),
    (∀ w, StatedQuadOdd n (fixedField U.val) (S₀ w) = ν * Q₀ w) ∧
    StatedClassicalModel (ProjOrthDerived Q₀) .POmegaOdd n ℓ (f / p) ∧
    TransportsToCoordinateField (oddIndexEquiv n) Q (coordinateQuadOdd n K) U S₀

@[expose] def PlusFieldDescent (n ℓ f p : ℕ) (Q : QuadraticForm K (Fin (2 * n) → K))
    (U : similarityPairs Q) (Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)) : Prop :=
  ∃ (ν : (fixedField U.val)ˣ)
    (S₀ : fixedSpace U.val ≃ₗ[fixedField U.val] (Fin n ⊕ Fin n → fixedField U.val)),
    (∀ w, StatedQuadPlus n (fixedField U.val) (S₀ w) = ν * Q₀ w) ∧
    StatedClassicalModel (ProjOrthDerived Q₀) .POmegaPlus n ℓ (f / p) ∧
    TransportsToCoordinateField (plusIndexEquiv n) Q (coordinateQuadPlus n K) U S₀

@[expose] def MinusFieldDescent (n ℓ f p : ℕ) (hn : 1 ≤ n) (Q : QuadraticForm K (Fin (2 * n) → K))
    (U : similarityPairs Q) (Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)) : Prop :=
  ∃ (b' c' : fixedField U.val), (∀ s : fixedField U.val, s ^ 2 + b' * s + c' ≠ 0) ∧
    ∃ (ν : (fixedField U.val)ˣ)
      (S₀ : fixedSpace U.val ≃ₗ[fixedField U.val]
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → fixedField U.val)),
      (∀ w, StatedQuadMinus n (fixedField U.val) b' c' (S₀ w) = ν * Q₀ w) ∧
      StatedClassicalModel (ProjOrthDerived Q₀) .POmegaMinus n ℓ (f / p) ∧
      TransportsToCoordinateField (minusIndexEquiv n hn) Q
        (coordinateQuadMinus n K hn (b' : K) (c' : K)) U S₀

@[expose] def OrthogonalFieldDescent (ℓ f p : ℕ) (Q : QuadraticForm K (Fin d → K))
    (Disp : ∀ U : similarityPairs Q,
      QuadraticForm (fixedField U.val) (fixedSpace U.val) → Prop)
    (a : MulAut (matrixProjectiveDerived Q)) : Prop :=
  p ∣ f ∧ ∀ σ : K ≃+* K,
    (∃ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = a ∧ g.val.right = σ) →
      orderOf σ = p ∧ Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p) ∧
      ∃ (U : similarityPairs Q) (c : Kˣ)
        (Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)),
        matrixProjectiveConjugationHom Q U = a ∧ U.val.right = σ ∧
        FixedFormDescent p Q U c Q₀ ∧ Disp U Q₀

end CFSG.RankThree.PartOne.KCOrthogonalDescent

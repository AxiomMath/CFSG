module

public import CFSG.Quasithin.Background.D2Thirteen
public import CFSG.Quasithin.EmptyFaithful.Vocabulary
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {V : Type*} [CommGroup V] [Finite V]

section SQTK

@[expose] def tcStronglyQuasithin (S : Type) [Group S] [Finite S] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Assembly.pRank p (⊤ : Subgroup S) ≤ 2

@[expose] def IsQuotientOfSQTKTC (X : Type*) [Group X] : Prop :=
  ∃ (S : Type) (_ : Group S) (_ : Finite S), tcStronglyQuasithin S ∧
    CFSG.SectionRank.IsKGroupCat S ∧ ∃ φ : S →* X, Function.Surjective φ

end SQTK

@[expose] def IsSumDecomposition (X G₁ G₂ : Subgroup (MulAut V)) (V₁ V₂ : Subgroup V) : Prop :=
  ∃ Q₁ Q₂ : Set (Subgroup (MulAut V)), QhatStar X = Q₁ ∪ Q₂ ∧ Disjoint Q₁ Q₂ ∧
    G₁ = ⨆ A ∈ Q₁, A ∧ G₂ = ⨆ A ∈ Q₂, A ∧ IsDirectSum ⊤ V₁ V₂ ∧ commV G₁ ≤ V₁ ∧
    commV G₂ ≤ V₂ ∧ commSub V₂ G₁ = ⊥ ∧ commSub V₁ G₂ = ⊥

@[expose] def HasSumDecomposition (X : Subgroup (MulAut V)) : Prop :=
  ∃ (G₁ G₂ : Subgroup (MulAut V)) (V₁ V₂ : Subgroup V), G₁ ≠ ⊥ ∧ G₂ ≠ ⊥ ∧
    IsSumDecomposition X G₁ G₂ V₁ V₂

@[expose] def IsIndecomposablePair (X : Subgroup (MulAut V)) : Prop :=
  X = Jhat X ∧ ¬ HasSumDecomposition X

@[expose] def sylow2Of (X : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | A ≤ X ∧ IsPGroup 2 A ∧ ¬ 2 ∣ (A.subgroupOf X).index}

@[expose] def IsOmegaFourPlus (X : Subgroup (MulAut V)) : Prop :=
  Nat.card V = 16 ∧ ∃ q : V → ZMod 2, IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧ IsPlusType q ∧
    ∀ g : MulAut V, g ∈ X ↔ g ∈ orthogonalGroupOf q ∧ Even (rk (commV (Subgroup.zpowers g)))

@[expose] def D217Concl (X : Subgroup (MulAut V)) (r : ℚ) : Prop :=
  (Nonempty (↥X ≃* DihedralGroup 3) ∧ (rk V : ℚ) = 2 * r ∧ (r = 1 ∨ r = 2)) ∨
  (Nonempty (↥X ≃* DihedralGroup 5) ∧ rk V = 4 ∧ r = 2) ∨
  (IsElemAbelian 3 (fittingOf X) ∧ Nat.card (fittingOf X) = 9 ∧
    (∃ t ∈ X, orderOf t = 2 ∧ (∀ f ∈ fittingOf X, t * f * t⁻¹ = f⁻¹) ∧
      X = fittingOf X ⊔ Subgroup.zpowers t) ∧ rk V = 4 ∧ r = 2) ∨
  (Nat.card (fittingOf X) = 27 ∧ (∀ f ∈ fittingOf X, f ^ 3 = 1) ∧
    (∃ f ∈ fittingOf X, ∃ g ∈ fittingOf X, f * g ≠ g * f) ∧
    (∃ t ∈ X, orderOf t = 2 ∧
      (∀ f ∈ fittingOf X, t * f * t⁻¹ * f ∈ (frattini ↥(fittingOf X)).map (fittingOf X).subtype) ∧
      X = fittingOf X ⊔ Subgroup.zpowers t) ∧ rk V = 6 ∧ r = 2) ∨
  (rk V = 4 ∧ IsOmegaFourPlus X ∧ Nonempty (↥X ≃* DihedralGroup 3 × DihedralGroup 3) ∧
    r = 3 / 2) ∨
  (IsElemAbelian 3 (fittingOf X) ∧ Nat.card (fittingOf X) = 27 ∧
    (∃ A : Subgroup (MulAut V), A ≤ X ∧ IsElemAbelian2 A ∧ Nat.card A = 4 ∧
      X = fittingOf X ⊔ A) ∧ rk V = 6 ∧ r = 3 / 2)

universe u in
@[expose] def D217 : Prop :=
  ∀ (V : Type u) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (r : ℚ), qhatOf X = (r : WithTop ℚ) → r ≤ 2 → X = Jhat X →
      commV (fittingOf X) = ⊤ → IsIndecomposablePair X →
      X ⊓ Subgroup.centralizer (fittingOf X : Set (MulAut V)) ≤ fittingOf X →
      pCoreOf 2 X = ⊥ → IsQuotientOfSQTKTC ↥X → QhatStar X = sylow2Of X ∧ D217Concl X r

end CFSG.Quasithin

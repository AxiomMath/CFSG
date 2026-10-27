module

public import CFSG.RankThree.PartOne.S11.PlaneData

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint.NativeSporadic (IsSporadic)

@[expose] def PlaneCentralizes {T : Type} [Group T] (E : Subgroup (MulAut T)) (U : Subgroup T) :
    Prop :=
  ∀ e ∈ E, ∀ u ∈ U, e u = u

@[expose] def ActualCoverAlternatingPlaneCentralization : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H) (n : ℕ), 5 ≤ n →
      Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin n)) →
      ∀ (p : ℕ) (E : Subgroup (MulAut (X ⧸ Subgroup.center X)))
        (U : Subgroup (X ⧸ Subgroup.center X)), PlaneOn p E U → PlaneCentralizes E U

@[expose] def ActualCoverOddClassicalPlaneCentralization : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H), CFSG.IsQuasisimple X →
      ∀ (t : StatedLieTag) (n ℓ f : ℕ), t ∈ classicalTags → ℓ.Prime → ℓ ≠ 2 → 1 ≤ f →
        StatedClassicalModel (X ⧸ Subgroup.center X) t n ℓ f →
        ∀ (p : ℕ) (E : Subgroup (MulAut (X ⧸ Subgroup.center X)))
          (U : Subgroup (X ⧸ Subgroup.center X)), PlaneOn p E U → PlaneCentralizes E U

@[expose] def ActualCoverOddG2PlaneCentralization : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H) (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f →
      ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 ℓ f →
      ∀ (p : ℕ) (E : Subgroup (MulAut (X ⧸ Subgroup.center X)))
        (U : Subgroup (X ⧸ Subgroup.center X)), PlaneOn p E U → PlaneCentralizes E U

@[expose] def OddF4ActualCoverLocalRankFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .F4 p f →
    (∃ u ∈ Y, orderOf u = 2 ∧ ∃ V : Subgroup X, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      CFSG.Assembly.IsElemAbelian p V ∧ Nat.card V = p ^ 4) ∧
      4 ≤ localRank p X ∧ 4 ≤ CFSG.twoLocalOddRank X

@[expose] def ActualCoverETypeRankThreeOnlyE6FieldTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.twoLocalOddRank X ≤ 3 →
    ∀ (Y : Subgroup X) (ℓ f : ℕ), ℓ.Prime → 1 ≤ f →
      ∀ τ : StatedLieTag, (τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6) →
        ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) τ ℓ f →
        τ = .E6 ∧ ℓ = 2 ∧ f = 1

@[expose] def ActualCoverHigherExceptionalSmallFieldRestrictions : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.twoLocalOddRank X ≤ 3 →
    ∀ (Y : Subgroup X) (ℓ f : ℕ), ℓ.Prime → 1 ≤ f →
      ∀ τ : StatedLieTag, (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨
          τ = .trialityD4) →
        ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) τ ℓ f →
        (ℓ ≠ 2 → τ ≠ .trialityD4 → ℓ ^ f = 3) ∧ (τ = .F4 → ℓ = 2 → ℓ ^ f = 2) ∧
          (τ = .trialityD4 → ℓ = 2 ∨ ℓ = 3) ∧ (τ = .F4 → ℓ ^ f = 2 ∨ ℓ ^ f = 3)

@[expose] def ActualCoverSporadicMovingPlaneFiveModelResidual : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H), CFSG.IsQuasisimple X →
      NativeSporadic.SporadicRep (X ⧸ Subgroup.center X) →
      ∀ (p : ℕ) (E : Subgroup (MulAut (X ⧸ Subgroup.center X)))
        (U : Subgroup (X ⧸ Subgroup.center X)), PlaneOn p E U → ¬ PlaneCentralizes E U →
        IsSporadic (X ⧸ Subgroup.center X) .Co1 ∨ IsSporadic (X ⧸ Subgroup.center X) .J4 ∨
          IsSporadic (X ⧸ Subgroup.center X) .Ly ∨ IsSporadic (X ⧸ Subgroup.center X) .Suz ∨
          IsSporadic (X ⧸ Subgroup.center X) .HN

@[expose] def LyLargePrimePlaneCentralization : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    IsSporadic T .Ly → ∀ (p : ℕ) (E : Subgroup (MulAut T)) (U : Subgroup T), PlaneOn p E U →
      p = 5 ∧ PlaneCentralizes E U

@[expose] def SuzLargePrimePlaneCentralization : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    IsSporadic T .Suz → ∀ (p : ℕ) (E : Subgroup (MulAut T)) (U : Subgroup T), PlaneOn p E U →
      p = 5 ∧ PlaneCentralizes E U

@[expose] def J4LargePrimePlaneCentralization : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    IsSporadic T .J4 → ∀ (p : ℕ) (E : Subgroup (MulAut T)) (U : Subgroup T), PlaneOn p E U →
      PlaneCentralizes E U

@[expose] def Co1ActualArbitraryCentralCoversForceTwoLocalRankFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (T : Type) [Group T] (π : Y →* T),
    Function.Surjective π → IsSporadic T .Co1 → π.ker ≤ Subgroup.center Y →
      4 ≤ CFSG.twoLocalOddRank X

@[expose] def MaximalMovingComponentHNQuotientsExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A, ¬ IsSporadic (L ⧸ Subgroup.center L) .HN

@[expose] def CharThreeTrialityActualCoverLocalRankFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (f : ℕ),
    ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .trialityD4 3 f →
    (∃ u ∈ Y, orderOf u = 2 ∧ ∃ V : Subgroup X, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      CFSG.Assembly.IsElemAbelian 3 V ∧ Nat.card V = 3 ^ 4) ∧
      4 ≤ localRank 3 X ∧ 4 ≤ CFSG.twoLocalOddRank X

@[expose] def SmallReeActualCoverNoLargePrimeAutomorphismPlane : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H) (ℓ f : ℕ), ReeTitsModel (X ⧸ Subgroup.center X) .twistedG2 ℓ f →
      ℓ = 3 ∧ f = 3 ∧ ∀ p : ℕ, p.Prime → 3 < p →
        ¬ p ^ 2 ∣ Nat.card (MulAut (X ⧸ Subgroup.center X)) ∧
        ∀ E : Subgroup (MulAut (X ⧸ Subgroup.center X)), CFSG.IsElementaryAbelian p E →
          Nat.card E ≠ p ^ 2

structure TenSevenInspections : Prop where
  alternating : ActualCoverAlternatingPlaneCentralization
  oddClassical : ActualCoverOddClassicalPlaneCentralization
  oddG2 : ActualCoverOddG2PlaneCentralization
  oddF4 : OddF4ActualCoverLocalRankFour
  eType : ActualCoverETypeRankThreeOnlyE6FieldTwo
  higherExceptional : ActualCoverHigherExceptionalSmallFieldRestrictions
  charThreeTriality : CharThreeTrialityActualCoverLocalRankFour
  smallRee : SmallReeActualCoverNoLargePrimeAutomorphismPlane
  sporadicResidual : ActualCoverSporadicMovingPlaneFiveModelResidual
  ly : LyLargePrimePlaneCentralization
  suz : SuzLargePrimePlaneCentralization
  j4 : J4LargePrimePlaneCentralization
  co1 : Co1ActualArbitraryCentralCoversForceTwoLocalRankFour
  hn : MaximalMovingComponentHNQuotientsExcluded

end CFSG.RankThree.PartOne

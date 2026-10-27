module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof418
public import CFSG.RankThree.PartTwo.Sec8.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Cases

variable {G : Type} [Group G] [Finite G]

@[expose] def Case83One (L : Subgroup G) (a : G) (A₀ : Subgroup G) (d : G) (n : ℕ) : Prop :=
  (IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n ∨
        IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * n)) ∧
      Nonempty (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n))) ∧
      (IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) n ∨
        (IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n ∧
          IsoPGUThree (barCentralizer (Subgroup.zpowers a) L) (2 ^ n) ∧
          ∃ a₀ ∈ A₀, a₀ ≠ 1 ∧ KFacts.InducesStdKind L a₀ .graphField ∧
            IsoGTwoEven (barCentralizer (Subgroup.zpowers a₀) L) n))

@[expose] def Case83Two (L : Subgroup G) (a : G) (_A₀ : Subgroup G) (d : G) (n : ℕ) : Prop :=
  IsoReeF4 (L ⧸ aschbacherSolvableCore 3 L) (3 * n) ∧
      IsoReeF4 (barCentralizer (Subgroup.zpowers a) L) n ∧
      IsoSUThree (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})))
        (2 ^ (3 * n))

@[expose] def Case83Three (L : Subgroup G) (a : G) (_A₀ : Subgroup G) (d : G) (n : ℕ) : Prop :=
  IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) ∧
      IsoSUThree (barCentralizer (Subgroup.zpowers a) L) (2 ^ n) ∧
      Nonempty (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n)))

@[expose] def Case83Four (L : Subgroup G) (a : G) (_A₀ : Subgroup G) (d : G) (n : ℕ) : Prop :=
  Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * n)) ∧
      IsoPGUThree (barCentralizer (Subgroup.zpowers a) L) (2 ^ n) ∧
      Nonempty (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n)))

@[expose] def Case83Five (L : Subgroup G) (a : G) (_A₀ : Subgroup G) (d : G) (n : ℕ) : Prop :=
  Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * n))) ∧
      Nonempty (barCentralizer (Subgroup.zpowers a) L ≃* projSp 2 (GaloisField 2 n)) ∧
      Nonempty (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n)))

theorem cases83_iff (L : Subgroup G) (a : G) (A₀ : Subgroup G) (d : G) (n : ℕ) :
    Cases83 L a A₀ d n ↔ Case83One L a A₀ d n ∨ Case83Two L a A₀ d n ∨ Case83Three L a A₀ d n ∨
      Case83Four L a A₀ d n ∨ Case83Five L a A₀ d n :=
  Iff.rfl

end Cases

@[expose] def Good88 {G : Type} [Group G] [Finite G] (Y : Subgroup G) (x d : G) : Prop :=
  IsQuasisimple (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
      aschbacherSolvableCore 3
        (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) ∧
    (∃ m : ℕ, 1 ≤ m ∧
      IsType418 (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
        aschbacherSolvableCore 3
          (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) m) ∧
    KFacts.InducesStdKind
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) x .field

@[expose] def KF88StepDOn
    (P : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → G → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      (∃ (A₀ : Subgroup G) (d' : G) (n' : ℕ), P G Y x A₀ d' n') →
      ∃ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x ∧ Good88 Y x d

@[expose] def KF88StepDCaseTwo : Prop := KF88StepDOn fun G _ _ => Case83Two

@[expose] def KF88StepDCaseFive : Prop := KF88StepDOn fun G _ _ => Case83Five

end CFSG.RankThree.PartTwo.Sec8

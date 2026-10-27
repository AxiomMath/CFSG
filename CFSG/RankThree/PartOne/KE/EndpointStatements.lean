module

public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion
public import CFSG.RankThree.PartOne.KC.TargetStatements

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint (ChevalleyExceptionalModel)
open CFSG.RankThree.Chevalley (exhaustionPhi)

@[expose] noncomputable def cycloVal (m ℓ f : ℕ) : ℤ :=
  (exhaustionPhi m).eval ((ℓ ^ f : ℕ) : ℤ)

@[expose] def OddEndpoint (τ : StatedLieTag) (Cond : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p → 1 ≤ f →
    Cond p ℓ f → ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    ChevalleyExceptionalModel (L ⧸ Subgroup.center L) τ ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    ComponentLocalCoreOddConclusion p E t L

@[expose] def EvenE7E8QPlusExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N → localRank p X ≤ 3 →
    ∀ L : Subgroup (X ⧸ N), IsComponent L → ∀ τ : StatedLieTag, (τ = .E7 ∨ τ = .E8) →
    ∀ f : ℕ, 1 ≤ f → ChevalleyExceptionalModel (L ⧸ Subgroup.center L) τ 2 f →
    ¬ p ∣ 2 ^ f + 1

structure F4Endpoints : Prop where
  evenQPlus : OddEndpoint .F4 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 2 ℓ f
  evenPhi3 : OddEndpoint .F4 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 3 ℓ f
  evenPhi4 : OddEndpoint .F4 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 4 ℓ f
  evenPhi6 : OddEndpoint .F4 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 6 ℓ f
  oddPhi3Phi6 : OddEndpoint .F4 fun p ℓ f =>
    ℓ ≠ 2 ∧ ((p : ℤ) ∣ cycloVal 3 ℓ f ∨ (p : ℤ) ∣ cycloVal 6 ℓ f)
  oddPhi4 : OddEndpoint .F4 fun p ℓ f => ℓ ≠ 2 ∧ (p : ℤ) ∣ cycloVal 4 ℓ f
  phi8Phi12 : OddEndpoint .F4 fun p ℓ f =>
    (p : ℤ) ∣ cycloVal 8 ℓ f ∨ (p : ℤ) ∣ cycloVal 12 ℓ f

structure E7Endpoints : Prop where
  phi3Phi6 : OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 3 ℓ f ∨ (p : ℤ) ∣ cycloVal 6 ℓ f
  phi4Phi12 : OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 4 ℓ f ∨ (p : ℤ) ∣ cycloVal 12 ℓ f
  phi8 : OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 8 ℓ f
  coxeter : OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 9 ℓ f ∨ (p : ℤ) ∣ cycloVal 18 ℓ f
  phi5Phi10 : OddEndpoint .E7 fun p ℓ f =>
    5 < p ∧ ((p : ℤ) ∣ cycloVal 5 ℓ f ∨ (p : ℤ) ∣ cycloVal 10 ℓ f)
  phi7Phi14 : OddEndpoint .E7 fun p ℓ f =>
    7 < p ∧ ((p : ℤ) ∣ cycloVal 7 ℓ f ∨ (p : ℤ) ∣ cycloVal 14 ℓ f)

structure E8Endpoints : Prop where
  phi3Phi6 : OddEndpoint .E8 fun p ℓ f => (p : ℤ) ∣ cycloVal 3 ℓ f ∨ (p : ℤ) ∣ cycloVal 6 ℓ f
  phi4 : OddEndpoint .E8 fun p ℓ f => (p : ℤ) ∣ cycloVal 4 ℓ f ∧ (p = 5 → ℓ = 2)
  phi8Phi12 : OddEndpoint .E8 fun p ℓ f => (p : ℤ) ∣ cycloVal 8 ℓ f ∨ (p : ℤ) ∣ cycloVal 12 ℓ f
  phi9Phi18 : OddEndpoint .E8 fun p ℓ f => (p : ℤ) ∣ cycloVal 9 ℓ f ∨ (p : ℤ) ∣ cycloVal 18 ℓ f
  phi15Phi30 : OddEndpoint .E8 fun p ℓ f =>
    (p : ℤ) ∣ cycloVal 15 ℓ f ∨ (p : ℤ) ∣ cycloVal 30 ℓ f
  phi5Phi10 : OddEndpoint .E8 fun p ℓ f =>
    5 < p ∧ ((p : ℤ) ∣ cycloVal 5 ℓ f ∨ (p : ℤ) ∣ cycloVal 10 ℓ f)
  phi7Phi14 : OddEndpoint .E8 fun p ℓ f =>
    7 < p ∧ ((p : ℤ) ∣ cycloVal 7 ℓ f ∨ (p : ℤ) ∣ cycloVal 14 ℓ f)
  phi20Phi24 : OddEndpoint .E8 fun p ℓ f =>
    (p : ℤ) ∣ cycloVal 24 ℓ f ∨ (5 < p ∧ (p : ℤ) ∣ cycloVal 20 ℓ f)

structure E6Endpoints : Prop where
  evenQPlus : OddEndpoint .E6 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 2 ℓ f
  phi3 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 3 ℓ f
  phi4 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 4 ℓ f
  phi6 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 6 ℓ f
  phi8 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 8 ℓ f
  phi9 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 9 ℓ f
  phi12 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 12 ℓ f
  phi5 : OddEndpoint .E6 fun p ℓ f => 5 < p ∧ (p : ℤ) ∣ cycloVal 5 ℓ f
  twPhi3 : OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 3 ℓ f
  twPhi4 : OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 4 ℓ f
  twPhi6 : OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 6 ℓ f
  twPhi8 : OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 8 ℓ f
  twPhi10 : OddEndpoint .twistedE6 fun p ℓ f => 5 < p ∧ (p : ℤ) ∣ cycloVal 10 ℓ f
  twPhi12 : OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 12 ℓ f
  twPhi18 : OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 18 ℓ f

end CFSG.RankThree.PartOne.KE

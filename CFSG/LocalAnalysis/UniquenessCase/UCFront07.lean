module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F07

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def Sec7Hyp (D : Data G) (p : ℕ) (H : Subgroup G) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ IsStronglyPEmbedded p D.M ∧ H ≠ ⊤ ∧ ¬ H ≤ D.M ∧ 1 < Open.pRank p (H ⊓ D.M)

@[expose] def PPrimeCoreIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (CFSG.pPrimeCore p ↥H).map H.subtype

@[expose] def Q7 (D : Data G) : Subgroup G :=
  pCoreOf 2 D.M

abbrev QuotK7 (p : ℕ) (H : Subgroup G) : Type :=
  ↥H ⧸ CFSG.pPrimeCore p ↥H

@[expose] def ImageModK (p : ℕ) (H L : Subgroup G) : Subgroup (QuotK7 p H) :=
  (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))

abbrev LKQuot7 (p : ℕ) (H : Subgroup G) : Type :=
  ↥(ImageModK p H (Opp p H))

@[expose] def PiPrimeCore (π : Set ℕ) (X : Subgroup G) : Subgroup G :=
  sSup {N : Subgroup G | N ≤ X ∧ (N.subgroupOf X).Normal ∧ ∀ q ∈ π, ¬ q ∣ Nat.card N}

@[expose] noncomputable def DerInf (X : Subgroup G) : Subgroup G :=
  (⨅ n : ℕ, derivedSeries ↥X n).map X.subtype

@[expose] def IsAutSz (X : Type) [Group X] (f : ℕ) : Prop :=
  ∃ (S : Type) (_ : Group S), IsSz S f ∧ Nonempty (X ≃* MulAut S)

@[expose] def IsReeType (X : Type) [Group X] (e : ℕ) : Prop :=
  Odd e ∧ (∀ S : Sylow 2 X, IsMulCommutative (S : Subgroup X)) ∧
    ∃ t : X, orderOf t = 2 ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 3 ^ e ∧
        Nonempty (↥(Subgroup.centralizer ({t} : Set X)) ≃* (Multiplicative (ZMod 2) × PSL(2, F)))

@[expose] def R71 (D : Data G) : Prop :=
  ∀ (p : ℕ) (H : Subgroup G), Sec7Hyp D p H →
    Odd (Nat.card (PPrimeCoreIn p H)) ∧ PPrimeCoreIn p H ≤ D.M ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card (PPrimeCoreIn p H) → Open.pRank q (PPrimeCoreIn p H) ≤ 3

@[expose] def R72 (D : Data G) : Prop :=
  ∀ (p : ℕ) (H : Subgroup G), Sec7Hyp D p H →
    genFittingFStar (QuotK7 p H) ≤ ImageModK p H (Opp p H) ∧
    ((∃ n : ℕ, LieModel (LKQuot7 p H) .PSL 2 p n) ∨
      (∃ n : ℕ, LieModel (LKQuot7 p H) .PSU 3 p n) ∨
      (p = 3 ∧ (IsReeType (LKQuot7 p H) 1 ∨ IsSpor (LKQuot7 p H) .M11 ∨ IsL3 (LKQuot7 p H) 2)) ∨
      (p = 5 ∧ (IsAutSz (LKQuot7 p H) 5 ∨ LieModel (LKQuot7 p H) .Tits 0 2 1 ∨
        IsSpor (LKQuot7 p H) .McL ∨ IsAlt (LKQuot7 p H) 10)) ∨
      (p = 11 ∧ IsSpor (LKQuot7 p H) .J4))

@[expose] def R76 (D : Data G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → IsStronglyPEmbedded p D.M →
    ∀ r : ℕ, r.Prime → ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian r E → Nat.card E = r ^ 2 →
      0 < Open.pRank p (D.M ⊓ centralizer (E : Set G)) →
      (∀ X : Subgroup G, X ≤ E → Nat.card X = r → 1 < Open.pRank p (D.M ⊓ normalizer (X : Set G))) →
        rankThreeGamma 1 r E ≤ D.M

@[expose] def R77 (D : Data G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → IsStronglyPEmbedded p D.M →
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig →
      ∀ X : Subgroup G, X ≤ D.M → IsPGroup r X → ¬ IsCyclic X → (∀ x ∈ X, x ^ r = 1) →
        ⁅⁅X, X⁆, X⁆ = ⊥ → 2 < Open.pRank p (D.M ⊓ normalizer (X : Set G)) →
        (¬ r ≡ 1 [MOD p] ∨ Open.pRank r X = 2 ∨ 3 < Open.pRank p (D.M ⊓ normalizer (X : Set G)) ∨
          (Open.pRank p D.M = Open.pRank p (D.M ⊓ normalizer (X : Set G)) ∧ p ∈ D.sig) ∨
          (D.M ≤ normalizer ((X ⊔ PiPrimeCore {r, p} D.M : Subgroup G) : Set G) ∧ p ∈ D.sig)) →
        rankThreeGamma 1 r X ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22.F07

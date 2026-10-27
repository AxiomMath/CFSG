module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Syl2Bar (D : Data G) (L : Subgroup G) : Subgroup (Bar2 L) :=
  ((NTL17 D L ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

@[expose] def K_FunRankTwo :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (r q : ℕ),
    r.Prime → r ≠ 2 →
    (∃ (t : StatedLieTag) (n f : ℕ),
      StatedLieAdmissible t n r f ∧ q = r ^ f ∧
        LieModel (X ⧸ Subgroup.center X) t n r f) →
    CFSG.Open.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) →
    (3 < q ∨ ¬ r ∣ Nat.card (Subgroup.center X)) →
    (¬ IsL2Over17 (X ⧸ Subgroup.center X) q) →
    (¬ IsL3EpsOdd17 (X ⧸ Subgroup.center X) r) →
    (¬ IsReeOver17 X q) →
    ∀ P : Sylow 2 X,
      (∃ E : Subgroup (X), ∃ K₁ K₂ : Subgroup (X),
        K₁ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
          K₂ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
        IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ E ≤ K₁ ⊔ K₂) ∧
      (q = r →
        (LieModel (X ⧸ Subgroup.center X) .G2 0 r 1 ∨
          LieModel (X ⧸ Subgroup.center X) .PSp 2 r 1) →
        ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ r ^ 2 - 1 →
          ∃ K₁ K₂ : Subgroup (X),
            K₁ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
              K₂ ∈ FunSet (fundPred q) X (P : Subgroup X) ∧
              ∃ E : Subgroup (X), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
                E ≤ K₁ ⊔ K₂)

@[expose] def K_LieOddRankFour :
    Prop :=
  (∀ (X : Type) [Group X] [Finite X] (r q : ℕ),
    r.Prime → r ≠ 2 →
    (∃ (t : StatedLieTag) (n f : ℕ),
      StatedLieAdmissible t n r f ∧ q = r ^ f ∧
        LieModel (X ⧸ Subgroup.center X) t n r f) →
    CFSG.Open.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) →
    (¬ IsL2Over17 (X ⧸ Subgroup.center X) q) →
    (¬ IsL3EpsOdd17 (X ⧸ Subgroup.center X) r) →
    (¬ IsReeOver17 X q) →
    4 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) ∨
      (q = r ∧ (LieModel (X ⧸ Subgroup.center X) .G2 0 r 1 ∨
        LieModel (X ⧸ Subgroup.center X) .PSp 2 r 1) ∧
        ¬ r ∣ Nat.card (Subgroup.center X)))

@[expose] def K_ReeSylowGeneration : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (q n : ℕ),
    IsReeOver17 X q → q = 3 ^ (2 * n + 1) → 1 ≤ n →
    Subgroup.center X = ⊥ ∧
      Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) ∧
    ∀ P : Sylow 2 X,
      CFSG.Open.IsElemAbelian 2 (P : Subgroup X) ∧ Nat.card (P : Subgroup X) = 8 ∧
      ∃ x y : X, x ∈ (P : Subgroup X) ∧ y ∈ (P : Subgroup X) ∧ x ≠ y ∧
        orderOf x = 2 ∧ orderOf y = 2 ∧
        let Kx : Subgroup X :=
          ⁅Subgroup.centralizer ({x} : Set X), Subgroup.centralizer ({x} : Set X)⁆
        let Ky : Subgroup X :=
          ⁅Subgroup.centralizer ({y} : Set X), Subgroup.centralizer ({y} : Set X)⁆
        IsL2Over17 ↥Kx q ∧ IsL2Over17 ↥Ky q ∧ CFSG.pCore 2 ↥Kx = ⊥ ∧
        CFSG.pCore 2 ↥Ky = ⊥ ∧ Subgroup.center Ky = ⊥ ∧
        Subgroup.centralizer ({x} : Set X) = Kx ⊔ Subgroup.zpowers x ∧
        Subgroup.centralizer ({y} : Set X) = Ky ⊔ Subgroup.zpowers y ∧
        IsCoatom (Subgroup.centralizer ({x} : Set X)) ∧
        IsCoatom (Subgroup.centralizer ({y} : Set X)) ∧ x ∈ Ky

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

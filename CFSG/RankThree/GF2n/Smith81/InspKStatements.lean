module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld

@[expose] def K2PSLStatement2 : Prop :=
  ∀ (Y : Type) [Group Y] (D : Set Y) (k f : ℕ), Hyp Y D → 3 ≤ k → 2 ≤ f →
    LieModel Y .PSL k 2 f → (∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) →
      ∀ d ∈ D, Nat.card (pCoreOf 2 (Subgroup.centralizer ({d} : Set Y))) ≤ (2 ^ f) ^ (2 * k - 3)

@[expose] def K2PSpStatement2 : Prop :=
  ∀ (Y : Type) [Group Y] (D : Set Y) (k f : ℕ), Hyp Y D → 3 ≤ k → 2 ≤ f →
    LieModel Y .PSp k 2 f → (∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) →
      ∀ d ∈ D,
        Nat.card (pCoreOf 2 (Subgroup.centralizer ({d} : Set Y))) ≤ (2 ^ f) ^ (2 * k - 1) ∨
          (Nat.card (pCoreOf 2 (Subgroup.centralizer ({d} : Set Y))) ≤ (2 ^ f) ^ (4 * k - 5) ∧
            Nat.card (Subgroup.centralizer ({d} : Set Y)) ∣
              (2 ^ f) ^ (4 * k - 5) * ordBC 1 (2 ^ f) * ordBC (k - 2) (2 ^ f))

@[expose] def KCOmegaStatement2 : Prop :=
  ∀ (Y : Type) [Group Y] (D : Set Y) (k f : ℕ), Hyp Y D → 5 ≤ k → 2 ≤ f →
    (∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) →
      (LieModel Y .POmegaPlus k 2 f → ∀ d ∈ D, Nat.card (Subgroup.centralizer ({d} : Set Y)) ∣
        (2 ^ f) ^ (4 * k - 7) * ordBC 1 (2 ^ f) * ordD (k - 2) (2 ^ f)) ∧
      (LieModel Y .POmegaMinus k 2 f → ∀ d ∈ D, Nat.card (Subgroup.centralizer ({d} : Set Y)) ∣
        (2 ^ f) ^ (4 * k - 7) * ordBC 1 (2 ^ f) * ordTwistedD (k - 2) (2 ^ f))

end CFSG.RankThree.GF2n.Smith81.Insp

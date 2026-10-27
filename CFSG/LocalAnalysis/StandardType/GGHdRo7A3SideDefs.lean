module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.HdRo7C
  CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def A3SideLabel {G : Type} [Group G] (X : Subgroup G) (m : ℕ) : Prop :=
  ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧
    lab.tag = .twA ∧ lab.n = 1 ∧ lab.rank + 1 = m

@[expose] def A3DiagModel {G : Type} [Group G] (Bs X : Subgroup G) (m : ℕ) : Prop :=
  ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (F : Type) (_ : Field F) (_ : Finite F)
    (φ : ↥(unitarySU 2 1 F m) →* ↥X), Nat.card F = 4 ∧ UnitTB.Model φ ∧
    ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t

@[expose] def A3RankLowerLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B X : Subgroup G) (z : G) (m : ℕ), p = 3 → 9 ≤ m →
    3 ∣ m → LargeEvenIsBmax p B → z ^ p = 1 → z ≠ 1 → X ≤ Subgroup.centralizer ({z} : Set G) →
    commutator ↥X = ⊤ → A3SideLabel X m → p ^ (m - 2) ≤ Nat.card B

@[expose] def A3RankUpperLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], ∀ m : ℕ, p = 3 →
    9 ≤ m → 3 ∣ m → A3SideLabel J (m - 3) → Nat.card Bs ≤ p ^ (m - 1)

@[expose] def A3SideTorLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs X : Subgroup G) (m : ℕ), p = 3 → 9 ≤ m → 3 ∣ m →
    GGBstar p B Bs → GGInnerDiagOn Bs X → commutator ↥X = ⊤ → A3SideLabel X m →
    p ^ (m - 2) ≤ Nat.card Bs → Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p ^ 2 →
    A3DiagModel Bs X m

@[expose] def A3SideMatLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs X : Subgroup G) (z : G) (m : ℕ),
    p = 3 → 9 ≤ m → 3 ∣ m → GGBstar p B Bs → A3DiagModel Bs X m → z ∈ Bs → z ≠ 1 →
    z ∈ Subgroup.centralizer (X : Set G) → Nat.card Bs ≤ p ^ (m - 1) →
    A3ModelAt p Bs X z ∧ ∀ e ∈ Bs ⊓ Subgroup.centralizer (X : Set G), e ∈ Subgroup.zpowers z

end CFSG.StandardType.HdRo7A3

module

public import CFSG.LocalAnalysis.StandardType.GGResAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGA5Label (lab : LargeEvenLabel) : Prop :=
  lab.rank = 5 ∧ ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1))

@[expose] def GGTBE6OrderInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs →
    ∀ [Fact p.Prime], p = 3 → ∀ X : Subgroup G,
      (X = L ∨ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧ X = K) →
      Nat.card ↥(ggAutomizer X Bs) = 51840 →
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGE6DepLabel lab ∧
        GGHasLabel lab (↥X ⧸ Subgroup.center ↥X)

@[expose] def GGE6DepJInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResE6DepShape p Bs L J K →
      ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ GGA5Label labJ ∧
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)

@[expose] def GGSchurDvdInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (lab : LargeEvenLabel), commutator X = ⊤ →
    LargeEvenInLambda2 lab → (GGE6DepLabel lab ∨ GGA5Label lab) →
    GGHasLabel lab (X ⧸ Subgroup.center X) → Nat.card ↥(Subgroup.center X) ∣ 12

end CFSG.StandardType

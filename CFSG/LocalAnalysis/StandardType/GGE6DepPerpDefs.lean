module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelResidualData
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGE6DepLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)

@[expose] def GGE6DepPerpCfg {G : Type} [Group G] (p : ℕ) (Bs L K : Subgroup G) : Prop :=
  p = 3 ∧ Nat.card Bs = 3 ^ 6 ∧ GGDependentReflectionDatum 3 Bs L K ∧
    ∃ lab₀ : LargeEvenLabel, GGE6DepLabel lab₀ ∧
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab = lab₀) ∧
      LargeEvenMarking K (fun lab _ _ _ _ _ => lab = lab₀)

@[expose] def GGE6DepPerpExcl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        ¬ GGE6DepPerpCfg p Bs L K

@[expose] def GGCoxeterLabelResidualOffE6DepInput : Prop :=
  GGCoxeterLabelResidualInputOn (fun _ _ p _ Bs L K => ¬ GGE6DepPerpCfg p Bs L K)

@[expose] def GGCorFiveTwentyInputQTwoOffE6Dep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQTwo p Bs L →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ¬ GGE6DepPerpCfg p Bs L K) →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

end CFSG.StandardType

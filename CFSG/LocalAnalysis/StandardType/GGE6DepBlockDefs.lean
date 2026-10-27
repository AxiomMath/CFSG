module

public import CFSG.LocalAnalysis.StandardType.GGE6DepPerpDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Defs

variable {G : Type} [Group G]

@[expose] def GGE6DepBlockCfg (p : ℕ) (Bs : Subgroup G) (x : G) (J : Subgroup G) (v : G) : Prop :=
  ∃ (w : G) (Dw N : Subgroup G) (n : G), w ∈ Bs ∧ w ^ p = 1 ∧ v * w = w * v ∧
    IsComponentOf Dw (Subgroup.centralizer ({v, w} : Set G)) ∧ p ∣ Nat.card Dw ∧
    N ≤ Dw ∧ N ≤ J ∧ ⁅N, N⁆ = N ∧ p ∣ Nat.card N ∧
    n ∈ Dw ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧ n * x * n⁻¹ ≠ x

end Defs

@[expose] def GGE6DepBlockCfgInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGE6DepPerpCfg p Bs L K → GGE6DepBlockCfg p Bs x J (x * y)

@[expose] def GGE6DepSecondNbr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGE6DepPerpCfg p Bs L K →
          ∃ (v : G) (X : Subgroup G), GGNbr p B x D J v X ∧
            Subgroup.zpowers v ≠ Subgroup.zpowers x ∧ Subgroup.zpowers v ≠ Subgroup.zpowers y

@[expose] def GGE6DepNbrPin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGE6DepPerpCfg p Bs L K →
          ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
            Subgroup.zpowers y' = Subgroup.zpowers y

end CFSG.StandardType

end

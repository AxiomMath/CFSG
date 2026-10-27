module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

@[expose] def FSLab (lab : LargeEvenLabel) : Prop :=
  lab.n = 1 ∧ ((lab.tag = .D ∧ lab.rank = 6) ∨ (lab.tag = .twD ∧ lab.rank = 7) ∨
    (lab.tag = .E7 ∧ lab.rank = 0))

@[expose] def IsEm (m : ℕ) {G : Type} [Group G] (X : Subgroup G) : Prop :=
  LargeEvenMarking X (fun lab _ _ _ _ _ =>
    ((m = 7 ∧ lab.tag = .E7) ∨ (m = 8 ∧ lab.tag = .E8)) ∧ lab.rank = 0 ∧ lab.n = 1)

@[expose] def FS81HypA {G : Type} [Group G] [Finite G] (b₀ : G) (K : Subgroup G) : Prop :=
  orderOf b₀ = 3 ∧
  K ≤ Subgroup.centralizer ({b₀} : Set G) ∧
    (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ Subgroup.center K = ⊥ ∧
    LargeEvenMarking K (fun lab _ _ _ _ _ => FSLab lab) ∧
  (∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S) ∧
  twoLocalPrimeRank 3 (Subgroup.centralizer ({b₀} : Set G)) = twoLocalPrimeRank 3 G ∧
  ∃ g : G, g * b₀ * g⁻¹ ∈ Subgroup.centralizer ({b₀} : Set G) ∧
    g * b₀ * g⁻¹ ∉ Subgroup.zpowers b₀

@[expose] def IsMaxElemAb3 {G : Type} [Group G] (C E : Subgroup G) : Prop :=
  E ≤ C ∧ IsElemAbelian 3 E ∧ ∀ E' : Subgroup G, E' ≤ C → IsElemAbelian 3 E' → E ≤ E' → E' = E

@[expose] def FS81ThmACRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCharTwoType G →
    ∀ (b₀ : G) (K E : Subgroup G) (m : ℕ), FS81HypA b₀ K →
      IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E → b₀ ∈ E → Nat.card E = 3 ^ m →
      7 ≤ m → 2 ^ m * m.factorial < Nat.card (ggAutomizer ⊤ E) → IsEm m (⊤ : Subgroup G)

@[expose] def FS81CentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCharTwoType G →
    ∀ (b₀ : G) (K E : Subgroup G) (m : ℕ), FS81HypA b₀ K →
      IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E → b₀ ∈ E → Nat.card E = 3 ^ m →
      7 ≤ m → 2 ^ m * m.factorial < Nat.card (ggAutomizer ⊤ E) →
        Subgroup.centralizer ({b₀} : Set G) = Subgroup.zpowers b₀ ⊔ K

@[expose] def LSS92TorusMaxInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), IsEm m (⊤ : Subgroup G) → IsSimpleGroup G →
    KProper InCatalog G →
    ∀ E : Subgroup G, IsElemAbelian 3 E → Nat.card E = 3 ^ m →
      IsCoatom (Subgroup.normalizer (E : Set G))

end CFSG.StandardType.FrameRoute

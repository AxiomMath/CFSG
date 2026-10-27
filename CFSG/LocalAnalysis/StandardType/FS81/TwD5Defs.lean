module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.SignalizerFunctorTheorem.Coprime.CommutatorGeneration

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

@[expose] def IsTwD5 {G : Type} [Group G] (K : Subgroup G) : Prop :=
  LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1)

@[expose] def HypTwD5 {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) : Prop :=
  orderOf b₀ = 3 ∧ K ≤ Subgroup.centralizer ({b₀} : Set G) ∧
    (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ Subgroup.center K = ⊥ ∧
    IsTwD5 K ∧
    (∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S) ∧
    twoLocalPrimeRank 3 (Subgroup.centralizer ({b₀} : Set G)) = twoLocalPrimeRank 3 G ∧
    (∃ g : G, g * b₀ * g⁻¹ ∈ Subgroup.centralizer ({b₀} : Set G) ∧
      g * b₀ * g⁻¹ ∉ Subgroup.zpowers b₀) ∧
    IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E ∧ b₀ ∈ E ∧ Nat.card E = 3 ^ 6 ∧
    2 ^ 6 * Nat.factorial 6 < Nat.card (ggAutomizer ⊤ E)

@[expose] def CanonTwD5 {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) : Prop :=
  Disjoint (Subgroup.zpowers b₀) (E ⊓ K) ∧ Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E ∧
    IsMaxElemAb3 K (E ⊓ K) ∧ Nat.card ↥(E ⊓ K) = 3 ^ 5 ∧
    Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K

@[expose] def StdTwD5 {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) : Prop :=
  IsSimpleGroup G ∧ HypTwD5 b₀ K E ∧ CanonTwD5 b₀ K E

@[expose] def RecOutTwD5 {G : Type} [Group G] [Finite G] (B : Basis3 G (5 + 1)) (b₀ : G) :
    Prop :=
  Nat.card ↥(ggAutomizer ⊤ B.span) = 103680 ∧
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 5 ∧
    (∀ A ∈ B.realized ⊤, (∀ j : Fin (5 + 1), j ≠ 0 → A 0 j = 0) ∧
      ∀ v : Coords (5 + 1), v 0 = 0 → ∑ i, (A.mulVec v) i ^ 2 = ∑ i, v i ^ 2) ∧
    ∀ e : Coords (5 + 1), e ≠ 0 → (IsConjLine b₀ (B.line e) ↔
      ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = 1)))

@[expose] def NineFourData {G : Type} [Group G] (B : Basis3 G (5 + 1)) (t : G) : Prop :=
  orderOf t = 2 ∧ t * B.b 0 * t⁻¹ = (B.b 0)⁻¹ ∧ t * B.b 1 * t⁻¹ = (B.b 1)⁻¹ ∧
    (∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t) ∧
    (∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({B.b 2} : Set G) →
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({B.b 2} : Set G) ≤
        Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.zpowers t) ∧
    ∀ H ∈ Coprime.hyperplanes 3 (Subgroup.closure (Set.range fun i : Fin 4 => B.b i.succ.succ)),
      ∃ c ∈ Subgroup.centralizer ({t} : Set G), c * B.b 2 * c⁻¹ ∈ H

end CFSG.StandardType.FrameRoute.FS81

end

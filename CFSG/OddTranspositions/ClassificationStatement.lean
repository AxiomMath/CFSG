module

public import CFSG.RankThree.GF2n.Tim79aSec23NoSq
public import CFSG.Timmesfeld.Transvection.Defs

public section

namespace CFSG.OddTranspositions

instance layer_characteristic_inst (G : Type*) [Group G] : (CFSG.layer G).Characteristic :=
  CFSG.LocalCores.layer_characteristic

instance layer_normal_inst (G : Type*) [Group G] : (CFSG.layer G).Normal :=
  inferInstance

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72

@[expose] def AscNoSqDichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G),
    (∃ d₀ : G, D = {g | IsConj d₀ g}) → IsOddTransp D →
    Subgroup.closure D = ⊤ →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    commutator G = layer G → IsPGroup 2 (G ⧸ layer G) →
    (¬ ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) →
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D ∨
      CFSG.Timmesfeld.Transvection.TransvectionHyp G
        {A | ∃ d ∈ D, A = Subgroup.zpowers d}

@[expose] def NoSqE1OrThreeTranspositions : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G),
    (∃ d₀ : G, D = {g | IsConj d₀ g}) → IsOddTransp D →
    Subgroup.closure D = ⊤ →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    commutator G = layer G → IsPGroup 2 (G ⧸ layer G) →
    (¬ ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) →
    ¬ CFSG.RankThree.GF2n.Tim79a.NoSqE1 D →
    ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)

@[expose] def ThreeTranspositionDichotomy : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), CFSG.Blueprint.Fischer.Pair G D →
    Subgroup.center G = ⊥ → IsSimpleGroup (commutator G) →
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D ∨
      CFSG.Timmesfeld.Transvection.TransvectionHyp G
        {A | ∃ d ∈ D, A = Subgroup.zpowers d}

@[expose] def F3Row : Prop :=
  ∀ (G : Type) [Group G] {D : Set G}, CFSG.Blueprint.Fischer.Pair G D →
    Subgroup.center G = ⊥ → IsSimpleGroup (commutator G) →
    ∀ (m : ℕ) (_hm : 5 ≤ m) (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)),
      (∀ x y, f x y = f y x) → (∀ x, (∀ y, f x y = 0) → x = 0) →
      CFSG.Open.fischerCentralQuotientModel D
        (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => f x y)
          fun v => f v v = 1))
        (CFSG.Open.fischerTransvections (fun x y => f x y) fun v => f v v = 1) →
      CFSG.RankThree.GF2n.Tim79a.NoSqE1 D ∨
        CFSG.Timmesfeld.Transvection.TransvectionHyp G
          {A | ∃ d ∈ D, A = Subgroup.zpowers d}

end CFSG.OddTranspositions

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_23Omega (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    ¬ IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)

@[expose] def S23_5_2Omega (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) →
      c.L = c.L0 ∧ c.n = 2 * CFSG.Open.pRank 2 D.Z

@[expose] def S23_26Omega (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) →
    ∀ P : Sylow 3 ↥(oTwoThreeOf D.M), (3 : ℕ) ∉ D.sig ∧ IsCyclic ↥P

@[expose] def S23_23OmegaCaseA {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) : Prop :=
  jOneOf D.T ≤ Subgroup.centralizer (c.V : Set G)

@[expose] def S23_23OmegaCaseB {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) : Prop :=
  CFSG.Open.pRank 2 D.Z = 2 ∧
    (∃ A₀ : Subgroup G, A₀ ≤ zJOneOf D.T ⊓ c.V ∧ Nat.card A₀ = 4 ∧
      ∃ x ∈ c.L, x ∈ Subgroup.normalizer (A₀ : Set G) ∧ x ∉ D.M) ∧
    ¬ ((D.T : Set G) ⊆ (c.L : Set G) * (centralizer (c.V : Set G) : Set G))

@[expose] def S23_23Cases (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) →
      (hV : IsElemAbelian 2 c.V) →
      NatOmegaMinus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) →
        S23_23OmegaCaseA c ∨ S23_23OmegaCaseB c

@[expose] def S23_23CaseA (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) →
      (hV : IsElemAbelian 2 c.V) →
      NatOmegaMinus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) →
        S23_23OmegaCaseA c → False

@[expose] def S23_23CaseB (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) →
      (hV : IsElemAbelian 2 c.V) →
      NatOmegaMinus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) →
        S23_23OmegaCaseB c → False

@[expose] def KOrdNatural : Prop :=
  (∀ {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {n : ℕ},
      IsNaturalClassicalModule H n → CFSG.pCore 2 ↥H = ⊥) ∧
  (∀ {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {n : ℕ},
      IsNaturalClassicalModule H n → Nontrivial ↥H) ∧
  (∀ {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {X : Type} [Group X] [Finite X]
      {n : ℕ}, IsNaturalClassicalModule H n → IsL2 X n → Nat.card ↥H = Nat.card X →
        CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n) ∧
  (∀ {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {X : Type} [Group X] [Finite X]
      {n : ℕ}, IsNaturalClassicalModule H n → IsOmegaMinus X 4 n →
        Nat.card ↥H = Nat.card X → NatOmegaMinus H ⊤ ⊥ 4 n)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

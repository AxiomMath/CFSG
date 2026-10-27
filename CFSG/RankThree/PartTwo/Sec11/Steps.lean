module

public import CFSG.RankThree.PartTwo.Sec11.Notation
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item112 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      ∃ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure {c, d} ∧
        (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≠ Subgroup.zpowers c

@[expose] def Item113 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y →
      A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} ∧
        IsCyclic (R ⊓ Sec4.thetaQuotCentralizer L : Subgroup G)

@[expose] def Item114 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y →
      ∀ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ A →
        ∃ w ∈ Subgroup.normalizer (A : Set G),
          (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom =
            (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom

@[expose] def Item115 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y →
      ¬ Sec21.IsIrreducibleOn (Sec4.autIn (Subgroup.normalizer (A : Set G)) A)

@[expose] def Item116 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y →
      ∀ B : Subgroup G, B ≤ A → Nat.card A = 3 * Nat.card B →
        ¬ (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G) ∧
          Sec21.IsIrreducibleOn (Sec4.autIn (Subgroup.normalizer (A : Set G)) B))

@[expose] def Item117 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      ∀ D : Subgroup G, D ≤ A → Nat.card D = 3 →
        (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G) ↔
          D = Subgroup.zpowers d)

end CFSG.RankThree.PartTwo.Sec11

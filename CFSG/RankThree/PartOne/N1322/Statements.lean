module

public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S12.Facts13

public section

namespace CFSG.RankThree.PartOne.N1322

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def DiffClass {G : Type} [Group G] (E L : Subgroup G) (t s : MulAut E) : Prop :=
  t ∈ torusImage E L ∧ s ∈ torusImage E L ∧ ∀ l ∈ torusImage E L, l * t * l⁻¹ ≠ s

@[expose] def KF1322Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E,
      Odd (orderOf (t * s)) → orderOf (t * s) = 1 ∨ orderOf (t * s) = 3

@[expose] def KF1322Kty : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    (RowModel p L 3 ∨ RowModel p L 4 ∨ RowModel p L 5 ∨ RowModel p L 6 ∨ RowModel p L 8) →
    ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, DiffClass E L t s →
      ∀ (g : G) (hg : g ∈ Subgroup.normalizer (E : Set G)),
        conjAut E g hg * t * (conjAut E g hg)⁻¹ ≠ s

@[expose] def KF1322G2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    RowModel p L 2 →
    ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, DiffClass E L t s →
      ∀ (y : G), y ∈ cNormalizer c → ∀ (hy : y ∈ Subgroup.normalizer (E : Set G)),
        conjAut E y hy * t * (conjAut E y hy)⁻¹ ≠ s

end CFSG.RankThree.PartOne.N1322

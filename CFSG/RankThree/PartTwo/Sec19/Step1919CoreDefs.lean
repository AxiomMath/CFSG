module

public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def Step1919CoreSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
      Nat.card (E ⊓ L : Subgroup G) = 9 →
      Sec4.IsExtOf
        (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) →
      ∀ H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G), H ≠ M →
        (∀ J ∈ scriptJ M H,
          (IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J)) ∧
          ((IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
              IsProperParabolic (starIm J H)) ∨
            (Nonempty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
              Sec4.IsExtOf (starIm J H) (Equiv.Perm (Fin 5))
                (Multiplicative (Fin 4 → ZMod 2))))) →
        (∀ J ∈ scriptJ M H, E ≤ Subgroup.normalizer (J : Set G)) →
        (∀ J ∈ scriptJ M H, ∃ j ∈ J, c * j * c⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M) →
        ∀ J ∈ scriptJ M H,
          (∀ g ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ⊓
              Subgroup.normalizer (E : Set G),
            (∃ k : ℕ, g ^ 3 ^ k = 1) → g ∈ Subgroup.normalizer (J : Set G)) →
          E ⊓ J ≠ E ⊓ L

@[expose] def Step1919CoreSplitLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
      Nat.card (E ⊓ L : Subgroup G) = 9 →
      Sec4.IsExtOf
        (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) →
      ∀ H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G), H ≠ M →
        (∀ J ∈ scriptJ M H,
          (IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J)) ∧
          ((IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
              IsProperParabolic (starIm J H)) ∨
            (Nonempty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
              Sec4.IsExtOf (starIm J H) (Equiv.Perm (Fin 5))
                (Multiplicative (Fin 4 → ZMod 2))))) →
        (∀ J ∈ scriptJ M H, E ≤ Subgroup.normalizer (J : Set G)) →
        (∀ J ∈ scriptJ M H, ∃ j ∈ J, c * j * c⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M) →
        ∀ J ∈ scriptJ M H,
          (∀ g ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ⊓
              Subgroup.normalizer (E : Set G),
            (∃ k : ℕ, g ^ 3 ^ k = 1) → g ∈ Subgroup.normalizer (J : Set G)) →
          IsProperParabolic (starIm J H) →
          (∀ e ∈ E, e ≠ 1 → ∃ j ∈ J, e * j * e⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M) →
          3 ^ 6 ∣ Nat.card (MulAut (J ⧸ CFSG.pCore 2 J)) →
          Subgroup.center (J ⧸ CFSG.pCore 2 J) = ⊥ →
          ((∃ n : ℕ, 1 ≤ n ∧
              (Nonempty (J ⧸ CFSG.pCore 2 J ≃*
                  Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
                Nonempty (J ⧸ CFSG.pCore 2 J ≃*
                  CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) ∨
                Nonempty (J ⧸ CFSG.pCore 2 J ≃*
                  CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 n)) ∨
                Sec8.IsoGTwoEven (J ⧸ CFSG.pCore 2 J) n)) ∨
            Nonempty (J ⧸ CFSG.pCore 2 J ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 3) ∨
            Nonempty (J ⧸ CFSG.pCore 2 J ≃* CFSG.Assembly.RankThreeEven.projSU 3 3 1)) →
          E ⊓ J ≠ E ⊓ L

end CFSG.RankThree.PartTwo.Sec19

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def IsA5A5Cyclic5 (X : Type) [Group X] : Prop :=
  ∃ e : ℕ, 1 ≤ e ∧ Nonempty (X ≃*
    (alternatingGroup (Fin 5) × alternatingGroup (Fin 5) × Multiplicative (ZMod (5 ^ e))))

@[expose] def P17_64_2 (D : Data G) (p n : ℕ) : Prop :=
  (IsL2Square (Bar2 (Lp D p)) n ∧ Sp D p ≠ ⊥) ∨
    (IsL2U3Product (Bar2 (Lp D p)) n ∧ Sp D p = ⊥)

@[expose] def R17_55At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G), L ≤ D.M → (L.subgroupOf D.M).Normal →
    ∀ n : ℕ, (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) →
      ∀ s : ℕ, Odd s → s ∣ n →
        ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 →
          ∀ X : Subgroup G, X ≤ L → Nat.card X = r →
            conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ D.M} ≠ conjSetOf D.M X

@[expose] def R17_56At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ p : ℕ, Hyp1754 D p →
    Opp p D.M = Lp D p ⊔ Sp D p ∨
      (p = 3 ∧ ∃ L ∈ calC D.M, IsL3 (Bar2 L) 2)

@[expose] def R17_57At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ p : ℕ, Hyp1754 D p → CFSG.Open.pRank p (Sp D p) ≤ 1

@[expose] def R17_58At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ p : ℕ, Hyp1754 D p → ∀ L ∈ calC D.M, ¬ IsL3 (Bar2 L) 2

structure Ctx17_58 (D : Data G) (V₀ V L : Subgroup G) (p : ℕ) : Prop where
  hyp125 : Hyp125 D V₀ V
  hyp54 : Hyp1754 D p
  memC : L ∈ calC D.M
  shapeL : IsL3 (Bar2 L) 2

@[expose] def R17_59At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (p : ℕ), Ctx17_58 D V₀ V L p →
    ∀ A : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 A L →
      CFSG.Open.rankThreeGamma 1 3 A ≤ D.M

@[expose] def R17_60At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (p : ℕ), Ctx17_58 D V₀ V L p → L ≠ Lp D p

@[expose] def R17_61At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (p : ℕ), Ctx17_58 D V₀ V L p →
    ∃ K ∈ calC (Lp D p), K ≠ L ∧
      ¬ ∃ n : ℕ, Odd n ∧ (IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n)

@[expose] def R17_62At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (p : ℕ), Ctx17_58 D V₀ V L p → D.k = 1

@[expose] def R17_63At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (p : ℕ), Ctx17_58 D V₀ V L p →
    ∀ K ∈ calC D.M, K ≠ L →
      ∃ n : ℕ, Odd n ∧ (IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n)

@[expose] def R17_64_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ p : ℕ, Hyp1754 D p → Hinf D.M = Lp D p

@[expose] def R17_64_2At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ p : ℕ, Hyp1754 D p → ∃ n : ℕ, P17_64_2 D p n

@[expose] def R17_64_3At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ p : ℕ, Hyp1754 D p → ∀ n : ℕ, P17_64_2 D p n →
    IsPowTwo n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]

@[expose] def R17_65At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ p : ℕ, p ∈ D.sig → (calL0Star D p).Nonempty

@[expose] def R17_65 (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V), R17_65At D V₀ V

@[expose] def R17_66_1At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G, X = conjClosure D.M L →
    X ∈ calL0Star D p → UniqueMax D.M L ∨ IsAlt (Bar2 L) 5

@[expose] def R17_67At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  V₀ ≠ ⊥ → ∀ p : ℕ, p ∈ D.sig →
    ∀ L ∈ calLp D p, ∀ X : Subgroup G, X = conjClosure D.M L →
      X ∈ calL0Star D p →
        IsU5 (Bar2 X) 2 ∨
        (∃ n : ℕ, IsPowTwo n ∧ IsU4 (Bar2 X) n) ∨
        (∃ n : ℕ, IsSp4 (Bar2 X) n ∧ SwapsParabolics D.T X) ∨
        (X ≠ L ∧ ∃ n : ℕ, IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∨
        (∃ n : ℕ, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n))

@[expose] def R17_68At (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ p : ℕ, p ∈ D.sig →
    ∀ L ∈ calLp D p, ∀ X : Subgroup G, X = conjClosure D.M L →
      X ∈ calL0Star D p → IsAlt (Bar2 L) 5 →
        p = 5 ∧ eM D.M = 3 ∧
          IsA5A5Cyclic5
            ↥(CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))) ∧
          Hinf (oTwoEOf D.M) ≤ Opp 5 D.M

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

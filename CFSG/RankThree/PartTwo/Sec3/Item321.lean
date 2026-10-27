module

public import CFSG.RankThree.PartTwo.Notation
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec3

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type*} [Group G]

@[expose] def thompsonOf (T : Subgroup G) : Subgroup G :=
  (CFSG.higherElemThompson T 0).map T.subtype

@[expose] def omegaZOf (Q : Subgroup G) : Subgroup G :=
  (CFSG.omegaOneCenter (⊤ : Subgroup Q)).map Q.subtype

structure IsChiefSeriesUnder (L V : Subgroup G) (r : ℕ) (Vs : Fin (r + 1) → Subgroup G) :
    Prop where
  zero : Vs 0 = ⊥
  last : Vs (Fin.last r) = V
  normalized : ∀ i, L ≤ Subgroup.normalizer (Vs i : Set G)
  lt : ∀ i : Fin r, Vs i.castSucc < Vs i.succ
  irreducible : ∀ (i : Fin r) (W : Subgroup G), Vs i.castSucc ≤ W → W ≤ Vs i.succ →
    L ≤ Subgroup.normalizer (W : Set G) → W = Vs i.castSucc ∨ W = Vs i.succ

@[expose] def IsNaturalFactorVia {F : Type*} [Field F] (L U W : Subgroup G)
    (α : L →* Matrix.SpecialLinearGroup (Fin 3) F) : Prop :=
  ∃ β : U →* Multiplicative (Fin 3 → F), Function.Surjective β ∧ β.ker = W.subgroupOf U ∧
    ∀ (ℓ : L) (u v : U), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β u))

@[expose] def Item321 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X L T : Subgroup G) (n : ℕ),
    CFSG.generalizedFitting X = CFSG.pCore 2 X → L ∈ oTwoComponentsIn X →
    X ≤ Subgroup.normalizer (L : Set G) →
    CFSG.ABGLocalTools.IsSylowOf 2 T X → L ⊔ T = X → Odd n →
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 n)) →
      (X ≤ Subgroup.normalizer (thompsonOf T : Set G) ∨
          ⁅omegaZOf (CFSG.Open.pCoreOf 2 X), L⁆ = ⊥) ∨
        (L ⊔ CFSG.Open.pCoreOf 2 X = X ∧
          ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
          ∃ α : L →* Matrix.SpecialLinearGroup (Fin 3) F, Function.Surjective α ∧
            α.ker = CFSG.pCore 2 L ∧
          ∀ (r : ℕ) (Vs : Fin (r + 1) → Subgroup G),
            IsChiefSeriesUnder L (omegaZOf (CFSG.Open.pCoreOf 2 X)) r Vs →
              (∀ i j k : Fin r, i < j → j < k → ¬ ⁅Vs i.succ, L⁆ ≤ Vs i.castSucc →
                ¬ ⁅Vs j.succ, L⁆ ≤ Vs j.castSucc → ¬ ⁅Vs k.succ, L⁆ ≤ Vs k.castSucc → False) ∧
              ∀ i : Fin r, ¬ ⁅Vs i.succ, L⁆ ≤ Vs i.castSucc →
                IsNaturalFactorVia L (Vs i.succ) (Vs i.castSucc) α)

@[expose] def Item321Split : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X L T : Subgroup G) (n : ℕ),
    CFSG.generalizedFitting X = CFSG.pCore 2 X → L ∈ oTwoComponentsIn X →
    X ≤ Subgroup.normalizer (L : Set G) →
    CFSG.ABGLocalTools.IsSylowOf 2 T X → L ⊔ T = X → Odd n →
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 n)) →
      (X ≤ Subgroup.normalizer (thompsonOf T : Set G) ∨
          ⁅omegaZOf (CFSG.Open.pCoreOf 2 X), L⁆ = ⊥) ∨
        L ⊔ CFSG.Open.pCoreOf 2 X = X

theorem item321Split_of_item321 (h : Item321) : Item321Split := by
  intro G _ _ X L T n hF hL hLN hT hLT hn hiso
  rcases h G X L T n hF hL hLN hT hLT hn hiso with h1 | ⟨h2, -⟩
  · exact Or.inl h1
  · exact Or.inr h2

end CFSG.RankThree.PartTwo.Sec3

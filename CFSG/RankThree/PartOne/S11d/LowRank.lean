module

public import CFSG.RankThree.PartOne.S11d.ThreeCompB
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.RankThree.PartOne.TCX.RankInterface

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix

@[expose] def LowRank : StatedLieTag → ℕ → Prop
  | .PSL, _ => True
  | .PSU, n => n ≤ 5
  | .PSp, n => n ≤ 3
  | .POmegaOdd, _ => True
  | .POmegaPlus, _ => False
  | .POmegaMinus, n => n ≤ 4
  | .G2, _ => True
  | .F4, _ => False
  | .E6, _ => False
  | .E7, _ => False
  | .E8, _ => False
  | .twistedE6, _ => False
  | .trialityD4, _ => True
  | .twistedB2, _ => True
  | .twistedG2, _ => True
  | .twistedF4, _ => True
  | .Tits, _ => True

@[expose] def HighRankFalse (t : StatedLieTag) : Prop :=
  CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels →
    ∀ (J : Type) [Group J] [Finite J] (p n f₀ : ℕ), CFSG.IsQuasisimple J → p.Prime → 5 ≤ p →
      1 ≤ f₀ → ¬ 2 ∣ Nat.card (Subgroup.center J) → ¬ p ∣ Nat.card (Subgroup.center J) →
      CFSG.Assembly.evenRank J ≤ 3 → LieModel (J ⧸ Subgroup.center J) t n 2 (p * f₀) →
      ¬ LowRank t n → False

@[expose] def ThreeCompBL (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    2 ≤ CFSG.pRank p T → ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) → LowRank t n →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel t n f₀ α →
    ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x →
      ∀ S : Subgroup T, S ≠ ⊥ → IsPGroup 2 ↥S → (∀ g ∈ S, α g ∈ S) →
        x ∈ Subgroup.normalizer (S : Set T) →
        ∃ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D ∧
          (∀ g ∈ D, α g ∈ D) ∧
          ∀ g ∈ Subgroup.centralizer ({x} : Set T), α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) →
            g ∈ D

@[expose] def FixedRankTL (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    2 ≤ CFSG.pRank p T → ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) → LowRank t n →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel t n f₀ α →
      2 ≤ CFSG.pRank p ↥(fixRes α)

theorem ThreeCompB.toL {t : StatedLieTag} (h : ThreeCompB t) : ThreeCompBL t :=
  fun T _ _ p hp hp5 hr h2 n f₀ hf₀ hM _ => h T p hp hp5 hr h2 n f₀ hf₀ hM

theorem FixedRankT.toL {t : StatedLieTag} (h : FixedRankT t) : FixedRankTL t :=
  fun T _ _ p hp hp5 hr h2 n f₀ hf₀ hM _ => h T p hp hp5 hr h2 n f₀ hf₀ hM

end CFSG.RankThree.PartOne.TCX

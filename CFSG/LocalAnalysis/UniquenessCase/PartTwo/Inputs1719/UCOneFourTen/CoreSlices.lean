module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.Core
import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreEvenSimple
public import CFSG.Foundations.KCoreOpen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

structure CoreSetup (X : Type) [Group X] [Finite X] (K L T Y : Subgroup X) (n : ℕ) : Prop where
  kGroup : CFSG.Open.IsKGroup X
  pRank_le : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3
  pCore_eq_bot : CFSG.pCore 2 X = ⊥
  quasisimple : CFSG.Open.IsQuasisimple ↥K
  normal : K.Normal
  centralizer_le : centralizer (K : Set X) ≤ K
  sup_eq_top : K ⊔ T = ⊤
  le : L ≤ K
  perfect : ⁅L, L⁆ = L
  sz : IsSz (Bar2 L) n
  ne_top : Y ≠ ⊤
  subnormal : CFSG.Open.IsSubnormal L Y
  sylow : IsSylowOf 2 T (F08.CentOverO2 Y L)
  normalizer_le : normalizer (T : Set X) ≤ Y
  normalizer_odd_le : ∀ A : Subgroup X, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
    normalizer (A : Set X) ≤ Y
  subnormal_of_le : ∀ X₁ : Subgroup X, X₁ ≠ ⊤ → L ≤ X₁ → T ≤ X₁ → CFSG.Open.IsSubnormal L X₁

@[expose] def CoreAltSlice : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K L T Y : Subgroup X) (n m : ℕ), CoreSetup X K L T Y n →
    Nonempty ((↥K ⧸ center ↥K) ≃* ↥(alternatingGroup (Fin m))) → False

@[expose] def CoreSporSlice : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K L T Y : Subgroup X) (n : ℕ) (s : TauCeti.SporadicName),
    CoreSetup X K L T Y n →
    Nonempty ((↥K ⧸ center ↥K) ≃* (TauCeti.CFSGIndex.sporadic s).Group) → False

@[expose] def CoreOddSlice : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K L T Y : Subgroup X) (n : ℕ)
    (d : TauCeti.ValidLieTypeIndex), CoreSetup X K L T Y n → d.1.characteristic ≠ 2 →
    Nonempty ((↥K ⧸ center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) → False

@[expose] def CoreOuterSlice : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K L T Y : Subgroup X) (n : ℕ), CoreSetup X K L T Y n →
    CFSG.Blueprint.EvenLieType (↥K ⧸ center ↥K) → CFSG.Open.pCoreOf 2 L = ⊥ →
    Odd (Nat.card ↥(K ⊓ centralizer (L : Set X))) → False

@[expose] def CoreParabolicSlice : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K L T Y : Subgroup X) (n : ℕ), CoreSetup X K L T Y n →
    CFSG.Blueprint.EvenLieType (↥K ⧸ center ↥K) → CFSG.Open.pCoreOf 2 L ≠ ⊥ → False

theorem uc1_4_10Core_of_slices
    (hAlt : CoreAltSlice) (hSpor : CoreSporSlice) (hOdd : CoreOddSlice)
    (hOuter : CoreOuterSlice) (hPar : CoreParabolicSlice) : UC1_4_10Core := by
  intro X _ _ K L T Y n hX hrank hO2 hKq hKn hCK hKT hLK hLp hSz hY hLY hSyl hNT hA hT2
  have hS : CoreSetup X K L T Y n :=
    ⟨hX, hrank, hO2, hKq, hKn, hCK, hKT, hLK, hLp, hSz, hY, hLY, hSyl, hNT, hA, hT2⟩
  rcases HardMathSupport.Timmesfeld.Coordinator.centralQuotient_family hKq (hX.subgroup K) with
    ⟨m, he⟩ | ⟨d, ⟨e⟩⟩ | ⟨s, he⟩
  · exact hAlt X K L T Y n m hS he
  · by_cases hd : d.1.characteristic = 2
    · obtain ⟨t, r, f, hm⟩ := StandardType.ChevTwo.exists_lieModel_two_of_valid d hd e
      have hev : CFSG.Blueprint.EvenLieType (↥K ⧸ center ↥K) := ⟨t, r, f, hm.admissible, hm⟩
      by_cases hL2 : CFSG.Open.pCoreOf 2 L = ⊥
      · by_cases hodd : Odd (Nat.card ↥(K ⊓ centralizer (L : Set X)))
        · exact hOuter X K L T Y n hS hev hL2 hodd
        · exact false_of_pCoreOf_eq_bot_of_even
            (ComponentClassification.CatLeaf.involutionCentralizersComponentFree_of_evenLieType hev)
            hO2 hKn hLK hSz hL2 hSyl hA hT2 (Nat.not_odd_iff_even.mp hodd)
      · exact hPar X K L T Y n hS hev hL2
    · exact hOdd X K L T Y n d hS hd ⟨e⟩
  · exact hSpor X K L T Y n s hS he

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

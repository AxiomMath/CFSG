module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213RestNN
public import CFSG.LocalAnalysis.UniquenessCase.UC6R3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213CovFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Pair108
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixNine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.Blueprint.LieModelAPI
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5Basic
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.Background.SmithC27Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

@[expose] def FiveCovers (X : Type) [Group X] : Prop :=
  F08.IsA6Z3 X ∨ F08.IsA7Z3 X ∨ F08.IsM22Z3 X ∨ PartTwo.Inputs1719.PartOne.IsSL3Four X ∨
    (IsSU3 X 3 ∧ Nat.card (center X) = 3)

@[expose] def S21_3RestNN4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ FiveCovers (Bar2 L) →
    ¬ D.M ≤ normalizer (L : Set G) →
    (∀ q : ℕ, q.Prime → q ≠ 2 → 2 ≤ CFSG.Open.pRank q L →
      q ∣ Nat.card (center (Bar2 L))) →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem s21_3RestNN_of_restNN4
    {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h63 : UC6.R6_3 D) (h69 : UC6.R6_9 D)
    (h76 : F07.R76Sig D) (h : S21_3RestNN4 D Ch) : S21_3RestNN D Ch := by
  intro hH c L hL hN hq hthin hr hemb
  by_cases hX : FiveCovers (Bar2 L)
  · obtain ⟨hZ, hZS, hAut, hm3⟩ := uc22s213_typeFacts_of_five hX
    have h1 := hemb (PartOne.Section8.isStronglyPEmbedded_three_of_not_le_normalizer hSg h63 h69
      h76 hL hN hr hZ hZS hAut hm3)
    have h2 := pRank_bar2_eq_of_odd (Y := L) Nat.prime_three (by norm_num)
    exfalso
    omega
  · exact h hH c L hL hX hN hq hthin hr hemb

theorem s21_3RestNN_dataOfSetup_of_restNN4
    (hSE : StronglyEmbeddedFive) (hSE3 : StronglyEmbeddedThree) (hS : RankThreeUC.Standing G)
    (hUC : rankThreeUC G) (hC : RankThreeUC.AGL81TheoremC G) (hK : UCK.K36)
    (S : RankThreeUC.Setup G) (Ch : Choice2011 G)
    (h : S21_3RestNN4 (PartTwo.Three.dataOfSetup hS S) Ch) :
    S21_3RestNN (PartTwo.Three.dataOfSetup hS S) Ch :=
  s21_3RestNN_of_restNN4 (UC6S846.sigmaStd_dataOfSetup hS S)
    (PartTwo.Three.r6_3_dataOfSetup hS hUC hC S) (PartTwo.Three.r6_9_dataOfSetup hS hUC hC hK S)
    (PartTwo.Three.r76Sig_dataOfSetup hSE hSE3 hS S) h

end CFSG.LocalAnalysis.UniquenessCase.UC22

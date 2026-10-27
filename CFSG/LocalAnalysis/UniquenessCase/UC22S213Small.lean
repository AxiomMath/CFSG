module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213SporTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S13d
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33OddExceptionalRanks
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33PartialRanks
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63LieOut
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I161a2
import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutCount
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.OutNoOdd
import CFSG.LargeExtraspecial.DW2AOut
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedSmall (M L : Subgroup G) : Prop :=
  (LieModel (BarInf L) .PSL 3 3 1 ∨ LieModel (BarInf L) .PSU 3 3 1 ∨
    ∃ p k : ℕ, p ≠ 3 ∧ LieModel (BarInf L) .G2 0 p (2 ^ k)) ∧ CFSG.Open.pRank 3 M ≤ 2

section Small

set_option linter.unusedSectionVars false


theorem uc22s213_not_centralizesBar_of_small (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hGA : GriessAllModelsStatement) {L : Subgroup G} (hL : L ∈ calC S.M)
    (hs : S21_3ClosedSmall S.M L) (h3 : CFSG.Open.pRank 3 L ≤ 2)
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  intro haL
  obtain ⟨hX, hm3⟩ := hs
  obtain ⟨hZ, hinn, h2⟩ : ¬ 3 ∣ Nat.card (center (Bar2 L)) ∧
      (∀ σ : MulAut (BarInf L), Odd (orderOf σ) →
        σ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) := by
    rcases hX with hX | hX | ⟨p, k, hp3, hX⟩
    ·
      have hout : Nat.card (Outer (BarInf L)) ∣ 2 ^ 1 := by
        rw [show Nat.card (Outer (BarInf L)) =
          (MulAut.conj : BarInf L →* MulAut (BarInf L)).range.index from rfl,
          CFSG.OddStandard.SmallF3.L33.l33_index_inner hX, pow_one]
      refine ⟨?_, fun σ hσ =>
        CFSG.EvenSporadicStandard.HSStd.InvCent.mem_range_conj_of_odd_orderOf_of_card_outer_dvd
          hout hσ, PartOne.Section8.two_le_pRank_three_of_lieModel_PSL_three_three_one hX⟩
      rw [center_bar2_eq_bot_of_row hL rfl rfl (griessRow_of_lieModel_classical hGA hX
        (by decide)), card_bot]
      norm_num
    ·
      refine ⟨?_, fun σ hσ => uc22s13d_out_mem_of_isPGroup
        (CFSG.LargeExtraspecial.DW.isPGroup_outer_psu hX) hσ (pow_orderOf_eq_one σ),
        PartOne.Section8.two_le_pRank_three_of_lieModel_PSU_three_three_one hX⟩
      rw [center_bar2_eq_bot_of_row hL rfl rfl (griessRow_of_lieModel_classical hGA hX
        (by decide)), card_bot]
      norm_num
    ·
      obtain ⟨hp, hf, -, hq3⟩ := CFSG.Blueprint.LieModel.admissible hX
      have hE : ∀ f : ℕ, exceptionalOrders .G2 0 p f = (2, 1) ∨
          exceptionalOrders .G2 0 p f = (1, 1) := by
        intro f
        unfold exceptionalOrders
        split <;> simp_all
      have hg : genericOrders .G2 0 p (2 ^ k) = (1, 1) := rfl
      have hrow := hGA (BarInf L) .G2 0 p (2 ^ k)
        (CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hX)
      have hZ2 : Nat.card (center (Bar2 L)) ∣ 2 := by
        rcases hE (2 ^ k) with hE | hE
        · simpa [hg, hE] using card_center_bar2_dvd_of_row hL (by rw [hg, hE]; norm_num) hrow
        · have h1 : Nat.card (center (Bar2 L)) ∣ 1 := by
            simpa [hg, hE] using card_center_bar2_dvd_of_row hL (by rw [hg, hE]; norm_num) hrow
          exact h1.trans (one_dvd 2)
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2
        (hX.chevalleyExceptionalModel (by decide)).2
      have hout : Nat.card (Outer (BarInf L)) ∣ 2 ^ (k + 1) := by
        rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
          pow_succ']
        exact PartOne.Section8.card_outer_adjointGroup_G2_dvd hp hf hK (by rw [hK]; exact hq3)
      refine ⟨fun h => absurd (Nat.le_of_dvd (by norm_num) (h.trans hZ2)) (by norm_num),
        fun σ hσ =>
          CFSG.EvenSporadicStandard.HSStd.InvCent.mem_range_conj_of_odd_orderOf_of_card_outer_dvd
            hout hσ, ?_⟩
      by_cases hp2 : p = 2
      · subst hp2
        exact (PartOne.Section8.pRank_three_eq_two_of_lieModel_G2_two hX).ge
      · exact (PartOne.Section8.pRank_three_eq_two_of_lieModel_G2_odd hp2 hp3 hX).ge
  have hL3 : CFSG.Open.pRank 3 L = 2 := by
    have := uc22s213_pRank_three_barInf hL.2.2 hZ
    omega
  have hp := uc22s213_pRank_le_one_of_centralizesBar (CFSG.Quasithin.A3.subnormal_le hL.1) hodd
    hpr haL S.hp.1.1 S.hp.1.2.1 hN
  have h1 := hk1 (uc22s213_strong_of_center hS hU S hσ hSE hOut hL hZ hinn hL3 hm3 hp)
  omega

end Small

end CFSG.LocalAnalysis.UniquenessCase.UC22

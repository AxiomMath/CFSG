module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Lift
import CFSG.LocalAnalysis.OddStandard.L2Ree.Mult
import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureSylowTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]


theorem uc22s2112r34_ree_false (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (h82 : F08.R82 D) (h211 : S21_1 D Ch) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {f : ℕ} (hm : LieModel (BarInf L) .twistedG2 0 3 f) : False := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hZ : center (Bar2 L) = ⊥ :=
    CFSG.OddStandard.L2Ree.ree_center_trivial hGA CFSG.TauCetiBridge.typewiseBridges
      (PartTwo.s15_Three_qs_of_open hL.2.2) (hm.of_mulEquiv e)
  have hZ3 : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by rw [hZ]; simp
  obtain ⟨-, hf3, hr⟩ :=
    CFSG.SectionRank.smallReeModel_rank (LieModel.reeTitsModel hm (by decide)).2
  have h3 : 3 ≤ CFSG.Open.pRank 3 L := by
    rw [← uc22s213_pRank_three_barInf hL.2.2 hZ3]
    omega
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    h82 L ⟨hL.1, hL.2.1, by omega, Or.inl (PartTwo.s15_Three_qs_of_open hL.2.2)⟩
  obtain ⟨e'⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 ((D.T ⊓ normalizer (L : Set G)) ⊓ L) L := by
    rw [inf_assoc, inf_eq_right.2 (le_normalizer : L ≤ normalizer (L : Set G))]
    exact uc22p2214_isSylowOf_inf D.sylowM hL.1
  obtain ⟨x, hxC, hx3, hxN⟩ := exists_mem_conjClosure_orderOf_mem_normalizer D.sylowM hL
    Nat.prime_three (by norm_num) hZ3
    (uc22s2112r34_exists_mem_normalizer (D.sylowM.isPGroup.to_le inf_le_left) inf_le_right hS
      (CFSG.OddStandard.L2Ree.kBase_of_lieModel_twistedG2 (hm.of_mulEquiv e')))
  have hXM : zpowers x ≤ D.M :=
    (zpowers_le.2 hxC).trans (PartTwo.TwelveTwentyThree.conjClosure_le hL.1.le)
  have hX3 : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
  exact not_mem_uniqueSet_of_le_normalizer D Ch h211 hH c (by rw [hX3]; exact Nat.prime_three)
    (by rw [hX3]; decide) hXM (zpowers_le.2 hxN)
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section8.mem_uniqueSet_of_isStronglyPEmbedded_three hstr
      hXM hX3)

theorem s21_12aFR34_of_rest (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (h82 : F08.R82 D) (h211 : S21_1 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hL3 : S21_12aFR34L3 D (Choice214U D)) (hF2 : S21_12aFR34F2 D (Choice214U D))
    (hF3 : S21_12aFR34F3 D (Choice214U D)) : S21_12aFR34 D (Choice214U D) :=
  s21_12aFR34_of_cases
    (fun hH c _ hL _ hm => uc22s2112r34_ree_false hGA h82 h211 hH (c.mono hCh) hL hm) hL3 hF2 hF3

end CFSG.LocalAnalysis.UniquenessCase.UC22

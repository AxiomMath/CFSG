module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtL34Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL34QuotientModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Quasithin.Background.B4ModelsLie
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.CommutatorSectionFaithful
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtDual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119
public import CFSG.Quasithin.Background.HTriU3
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB45SL3Outer
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs520
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5115
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114
public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Quasithin.Vol2.Ch6Defs
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.Quasithin.Background.F918V3QB1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem s16nt_row_l34 {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hirr : commSub ⊤ L ∈ irrSet L)
    (h : IsLn ↥L 3 2 ∧ E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = 9) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  classical
  have hirr' := hirr
  rw [irrSet, Set.mem_setOf_eq] at hirr'
  obtain ⟨hcommU, hIirr⟩ := hirr'
  have hHU : L ≤ stabSub (commSub ⊤ L) :=
    CFSG.Quasithin.le_stabSub_of_forall_mem hIirr.2.1
  have hne : ¬ L ≤ centSub (commSub ⊤ L) := by
    intro hHc
    have hUfix : commSub ⊤ L ≤ fixV L := fun u hu h hh => hHc hh u hu
    have hbot : commSub (commSub ⊤ L) L = ⊥ := commSub_eq_bot_iff.mpr hUfix
    rw [hcommU] at hbot
    have hlt := hIirr.1
    rw [hbot] at hlt
    simp only [bot_inf_eq] at hlt
    exact absurd hlt (lt_irrefl _)
  have hsimpleL : IsSimpleGroup ↥L :=
    CFSG.Quasithin.H13.E54.isSimpleGroup_of_lieModel h.1
  have hfaith : L ⊓ centSub (commSub ⊤ L) = ⊥ :=
    inf_centSub_eq_bot_of_isSimpleGroup hsimpleL hHU hne
  let HU : Subgroup (MulAut ↥(commSub ⊤ L)) := autSub L (commSub ⊤ L)
  have hWU : ∀ u : ↥(commSub ⊤ L), u ^ 2 = 1 :=
    fun u => Subtype.ext (by simpa using hW2 (u : W))
  have hHUisLn : IsLn ↥HU 3 2 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (autSubEquivOfFaithful hHU hfaith) h.1
  have hcommHU : commSub (⊤ : Subgroup ↥(commSub ⊤ L)) HU = ⊤ :=
    commSub_top_autSub_eq_top hHU hcommU
  have hdimHU : E3.mQuot (⊤ : Subgroup ↥(commSub ⊤ L)) (fixV HU) = 9 := by
    have hrel := Subgroup.relIndex_map_map_of_injective (fixV HU)
      (⊤ : Subgroup ↥(commSub ⊤ L)) (commSub ⊤ L).subtype_injective
    rw [map_subtype_fixV_autSub hHU, Subgroup.map_top, Subgroup.range_subtype] at hrel
    unfold E3.mQuot
    rw [← hrel]
    exact h.2
  have hirrHU : commSub (⊤ : Subgroup ↥(commSub ⊤ L)) HU ∈ irrSet HU :=
    mem_irrSet_autSub_of_mem_irrSet hHU hirr
  have hmodel : BinaryNineTensor HU ⊤ (fixV HU) 1 :=
    binaryNineTensor_of_l34_quotient_rank_nine hWU hHUisLn hcommHU hirrHU hdimHU
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, hReal⟩ := hmodel
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hK : Nat.card K = 4 := by simpa using hKcard
  have hgoal : 3 * rk ↥(fixV HU) ≤ rk ↥(⊤ : Subgroup ↥(commSub ⊤ L)) :=
    s16nt_goal_of_model (D := FFModel.twistTensor 1 (StatedSL 3 K)) (c := 3) (d := 9)
      (s16nt_cover_l34 (K := K) hK) (by norm_num) (s16nt_card_l34Mod (K := K) hK)
      hWU hcommHU le_rfl hReal
  rwa [CFSG.Quasithin.rk_fixV_autSub hHU, CFSG.Quasithin.rk_top] at hgoal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

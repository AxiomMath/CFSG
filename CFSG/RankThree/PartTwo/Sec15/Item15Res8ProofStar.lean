module

public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofUse
public import CFSG.RankThree.PartTwo.Sec16.Item166Res2Proof
public import CFSG.RankThree.PartTwo.Sec16.Item166Res4ProofOmg

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step1610Y4Star (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY3Star A LB, oPrimeResidualOf 3 Y ≠ ⊥ → ∃ X ∈ scriptY4 A LB, X ≤ Y

namespace Proof15Res8Star

theorem delta_normalizer_mem_scriptY3 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY3 A (lB A)) :
    delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) ∈ scriptY3 A (lB A) ∧
      Y ≤ delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hM2, -, hYM⟩ := Y4Core.twoLocal_facts h hY.1
  set M := Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) with hM
  have hYD : Y ≤ delta A (lB A) M := hY.2.le.trans (delta_mono hYM)
  have hO : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 (delta A (lB A) M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYD) (delta_le M)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  refine ⟨⟨⟨Y4Core.delta_mem_scriptY hM2.1, fun h0 => hY.1.2 (le_bot_iff.mp (h0 ▸ hO))⟩,
    (delta_delta M).symm⟩, hYD⟩

theorem eq_delta_normalizer_of_mem_scriptY3Star {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY3Star A (lB A)) :
    Y = delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) := by
  obtain ⟨hD3, hYD⟩ := delta_normalizer_mem_scriptY3 h hY.prop
  exact le_antisymm hYD (hY.2 hD3 hYD)

end Proof15Res8Star

open Proof15Res8Star

theorem step1610Y4Star_of_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) {A L : Subgroup G}
    {c : G} (h : Sec15R G A c L) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) :
    Step1610Y4Star A (lB A) := by
  intro Y hY hO
  obtain ⟨hM2, hF, -⟩ := Y4Core.twoLocal_facts h.toSec14Std hY.prop.1
  have hYeq := eq_delta_normalizer_of_mem_scriptY3Star h.toSec14Std hY
  obtain ⟨-, hJ, hOle, -⟩ := Y4Core.exists_mem_scriptY0 hRead hMem h hbot hM2 hF
  rw [← hYeq] at hJ hOle
  obtain ⟨J, hJ'⟩ := Y4Core.nonempty_of_le_sSup hOle hO
  exact ⟨J, (hJ J hJ').2.1, Y4Core.le_of_mem_comp3In hJ'⟩

theorem ctr166_of_omg_star {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hY4 : Step1610Y4Star A (lB A)) (h152 : Item152 A (lB A))
    (h155 : Item155 A (lB A)) (hΩ : Omg166Ctr A Y₀) : Ctr166 A Y₀ := by
  intro X hX hns hsol hK
  by_contra hXM
  obtain ⟨X', hX'4, hX'X⟩ := hY4 X hX hK
  exact hXM (Proof166Res3.le_M_of_omg h h152 h155 hX.prop hX'4 hX'X
    (hΩ X hX hns hsol hK hXM X' hX'4 hX'X))

theorem omega166_of_omg_star {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hY4 : Step1610Y4Star A (lB A)) (h152 : Item152 A (lB A))
    (h155 : Item155 A (lB A)) (hΩ : Omg166Sz A Y₀) (hthree : Omega166Three A Y₀) :
    Omega166 A Y₀ := by
  intro K₀ Z hK₀ hSz hK₀Z hZ
  by_cases hO : oPrimeResidualOf 3 Z = ⊥
  · exact hthree K₀ Z hK₀ hSz hK₀Z hZ hO
  · by_contra hZM
    obtain ⟨X', hX'4, hX'Z⟩ := hY4 Z hZ hO
    exact hZM (Proof166Res3.le_M_of_omg h h152 h155 hZ.prop hX'4 hX'Z
      (hΩ K₀ Z hK₀ hSz hK₀Z hZ hO hZM X' hX'4 hX'Z))

theorem step1610Y4Star_of_core_s17 (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    (hbot : Item145BotS17) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) : Step1610Y4Star A (lB A) :=
  step1610Y4Star_of_core hRead hMem h.toSec15R (hbot G A c L Y₀ h)

theorem step166CtrOther_of_omg_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    (hbot : Item145BotS17) (h152 : Item152R) (h155 : Item155R) (hΩ : Step166OmgOther) :
    Step166CtrOther := fun G _ _ A c L Y₀ h hL hJ =>
  ctr166_of_omg_star h (step1610Y4Star_of_core_s17 hRead hMem hbot h) (h152 G A c L h.toSec15R)
    (h155 G A c L h.toSec15R) (omg166Ctr_of_omg166 (hΩ G A c L Y₀ h hL hJ))

theorem step166CtrHJ_of_omg_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    (hbot : Item145BotS17) (h152 : Item152R) (h155 : Item155R) (hΩ : Step166OmgCtrHJ) :
    Step166CtrHJ := fun G _ _ A c L Y₀ h hJ =>
  ctr166_of_omg_star h (step1610Y4Star_of_core_s17 hRead hMem hbot h) (h152 G A c L h.toSec15R)
    (h155 G A c L h.toSec15R) (hΩ G A c L Y₀ h hJ)

theorem step166OmegaOther_of_omg_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    (hbot : Item145BotS17) (h152 : Item152R) (h155 : Item155R) (hΩ : Step166OmgOther)
    (hthree : Step166OmegaThreeOther) : Step166OmegaOther := fun G _ _ A c L Y₀ h hL hJ =>
  omega166_of_omg_star h (step1610Y4Star_of_core_s17 hRead hMem hbot h)
    (h152 G A c L h.toSec15R) (h155 G A c L h.toSec15R)
    (omg166Sz_of_omg166 (hΩ G A c L Y₀ h hL hJ)) (hthree G A c L Y₀ h hL hJ)

theorem step166OmegaHJ_of_omg_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    (hbot : Item145BotS17) (h152 : Item152R) (h155 : Item155R) (hΩ : Step166OmgSzHJ)
    (hthree : Step166OmegaThreeHJ) : Step166OmegaHJ := fun G _ _ A c L Y₀ h hJ =>
  omega166_of_omg_star h (step1610Y4Star_of_core_s17 hRead hMem hbot h)
    (h152 G A c L h.toSec15R) (h155 G A c L h.toSec15R) (hΩ G A c L Y₀ h hJ)
    (hthree G A c L Y₀ h hJ)

theorem step166CtrHJ_of_a5_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    (hbot : Item145BotS17) (h152 : Item152R) (h155 : Item155R) (hN : Step166OmgNotA5HJ)
    (hA5 : Step166CtrA5HJ) : Step166CtrHJ :=
  step166CtrHJ_of_omg_core hRead hMem hbot h152 h155 fun G _ _ A c L Y₀ h hJ =>
    omg166Ctr_of_a5 (hN G A c L Y₀ h hJ) (hA5 G A c L Y₀ h hJ)

theorem step166OmegaHJ_of_a5_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    (hbot : Item145BotS17) (h152 : Item152R) (h155 : Item155R) (hN : Step166OmgNotA5HJ)
    (hA5 : Step166OmegaA5HJ) (hthree : Step166OmegaThreeHJ) : Step166OmegaHJ :=
  step166OmegaHJ_of_omg_core hRead hMem hbot h152 h155
    (fun G _ _ A c L Y₀ h hJ =>
      omg166Sz_of_a5 (hN G A c L Y₀ h hJ) (hA5 G A c L Y₀ h hJ)) hthree

section Res4

theorem step166CtrNot2n_of_core (hRead : Y4CoreReadR)
    (hMem : Y4CoreMemR) (h152 : Item152R) (h155 : Item155R) (h148 : Item148R)
    (hbot : Item145BotS17) (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hA5 : Step166CtrA5HJ) : Step166CtrNot2n :=
  step166CtrNot2n_of
    (step166CtrHJ_of_a5_core hRead hMem hbot h152 h155
      (step166OmgNotA5HJ_of h148 hbot h1514 hMeets) hA5)
    (step166CtrOther_of_omg_core hRead hMem hbot h152 h155
      (step166OmgOther_of h148 hbot h1514 hMeets))

theorem step166OmegaNot2n_of_core (hRead : Y4CoreReadR)
    (hMem : Y4CoreMemR) (h152 : Item152R) (h155 : Item155R) (h148 : Item148R)
    (hbot : Item145BotS17) (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hA5 : Step166OmegaA5HJ) (hthree : Step166OmegaThreeOther)
    (hthreeHJ : Step166OmegaThreeHJ) : Step166OmegaNot2n :=
  step166OmegaNot2n_of
    (step166OmegaHJ_of_a5_core hRead hMem hbot h152 h155
      (step166OmgNotA5HJ_of h148 hbot h1514 hMeets) hA5 hthreeHJ)
    (step166OmegaOther_of_omg_core hRead hMem hbot h152 h155
      (step166OmgOther_of h148 hbot h1514 hMeets) hthree)

end Res4

end CFSG.RankThree.PartTwo.Sec16

module

import CFSG.RankThree.PartTwo.Sec15.Sylow155R1V
import CFSG.RankThree.PartTwo.Sec15.Sylow155B1
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem x_le_oPrimeResidualOf_delta {A X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    X ≤ oPrimeResidualOf 3 (delta A (lB A) M) := by
  have hX : oPrimeResidualOf 3 X = X := by
    rw [← hC.res]
    exact Proof155R2.oPrimeResidualOf_idem 3 Y
  rw [← hX]
  exact Sec15.oPrimeResidualOf_mono 3 (Sylow155B1.x_le_delta hC)

theorem isCharacteristicP_x_and_pCoreOf_ne_bot {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) {X K Y M T : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) :
    IsCharacteristicP 2 ↥X ∧ CFSG.Open.pCoreOf 2 X ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMchar, hME⟩ := charTwo_and_le_normalizer_oPrimeResidualOf h h149 hC
  have hEI : oPrimeResidualOf 3 (delta A (lB A) M) ≤ delta A (lB A) M :=
    Sec14.oPrimeResidualOf_le_self 3 _
  have hEchar : IsCharacteristicP 2 ↥(oPrimeResidualOf 3 (delta A (lB A) M)) :=
    Sec15.isCharacteristicP_of_le_normalizer (hEI.trans (delta_le M)) hME hMchar
  have hXchar : IsCharacteristicP 2 ↥X :=
    Sec15.isCharacteristicP_of_le_normalizer (x_le_oPrimeResidualOf_delta hC) (hEI.trans hIX)
      hEchar
  refine ⟨hXchar, ?_⟩
  have hX4 : X ∈ Sec15.scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hq := hX4.2.2.2
  haveI : Nontrivial ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸ Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    hq.2.1.toNontrivial
  haveI : Nontrivial (↥X ⧸ CFSG.pCore 2 ↥X) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X))).nontrivial
  haveI : Nontrivial ↥X := (QuotientGroup.mk_surjective (s := CFSG.pCore 2 ↥X)).nontrivial
  exact Sec15.pCoreOf_ne_bot_of_pCore_ne_bot (Sec15.pCore_ne_bot_of_isCharacteristicP hXchar)

theorem eq_normalizer_x_of_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) {X K Y M T : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hMX : M ≤ Subgroup.normalizer (X : Set G)) :
    M = Subgroup.normalizer (X : Set G) ∧
      M = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX2 := (isCharacteristicP_x_and_pCoreOf_ne_bot h h149 hC hIX).2
  have hMX' : M = Subgroup.normalizer (X : Set G) := Sec15.eq_normalizer_of_le hC.mem_m.1 hMX hX2
  refine ⟨hMX', Sec15.eq_normalizer_of_le hC.mem_m.1
    (hMX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)) ?_⟩
  have hR2 : CFSG.Open.pCoreOf 2 (CFSG.Open.pCoreOf 2 X) = CFSG.Open.pCoreOf 2 X := by
    refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X)
  rw [hR2]
  exact hX2

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

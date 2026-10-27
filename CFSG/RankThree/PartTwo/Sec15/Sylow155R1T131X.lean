module

import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T129
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T131
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofCases
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_two_le_delta_of_eq_sup_x {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hbot : Item145BotS14) (h444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K) :
    CFSG.Open.pCoreOf 2 K ≤ delta A (lB A) (CFSG.Open.pCoreOf 2 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.Open.pCoreOf 2 K with hVdef
  set U := CFSG.Open.pCoreOf 2 X with hUdef
  have hK : K ∈ scriptY4 A (lB A) := hC.mem_k.prop.1
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hVI : V ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, Sec15.isPiSubgroup_piCompl_three_of_isPGroup Nat.prime_two (by norm_num)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K),
      hK.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)⟩
  have hKV : ⁅K, V⁆ ≤ delta A (lB A) V := by
    have h := commutator_deltaZero_le_delta_of_le_normalizer hR.isE27 h444 h146 hK.2.2.1.le hVI
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    rwa [← Proof1515.eq_deltaZero_of_mem_scriptY4 hbot hR hK] at h
  have hXY : X ≤ Y := by
    have h := Sec14.oPrimeResidualOf_le_self 3 Y
    rwa [hC.res] at h
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    have hY := Sec14.le_normalizer_oPrimeResidualOf (p := 3)
      (Subgroup.le_normalizer : Y ≤ Subgroup.normalizer (Y : Set G))
    rwa [hC.res] at hY
  have hUR : U ≤ CFSG.Open.pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXY)
      (hYX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X)
  have hUQ : U ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hE.mem_p.prop.1.1 (hUR.trans hRP)
      (hX4.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
  have hV129 := pCoreOf_two_eq_commutator_sup hKX hK.2.1.symm
  calc V = ⁅X, V⁆ ⊔ U := hV129
    _ ≤ delta A (lB A) V :=
      sup_le ((Subgroup.commutator_mono hC.le_k le_rfl).trans hKV)
        (le_delta hUQ (le_sup_right.trans hV129.ge))

theorem pCoreOf_two_mem_scriptQ_of_eq_sup_x {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hbot : Item145BotS14) (h444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K) :
    CFSG.Open.pCoreOf 2 K ∈ scriptQ A (lB A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : K ∈ scriptY4 A (lB A) := hC.mem_k.prop.1
  have hV : CFSG.Open.pCoreOf 2 K ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, Sec15.isPiSubgroup_piCompl_three_of_isPGroup Nat.prime_two (by norm_num)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K),
      hK.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)⟩
  exact mem_scriptQ_of_le (delta_mem_scriptQ hR.isE27 h146 hV)
    (pCoreOf_two_le_delta_of_eq_sup_x hR hbot h444 h146 hC hE hRP hKX) hV.2.2

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

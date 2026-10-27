module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3SU3G4RankTwo

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryCover
import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
import CFSG.LocalAnalysis.UniquenessCase.UCKU3Key
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34U3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBU3
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl3
import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing)
open Subgroup Matrix CFSG.Open
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

variable {G : Type} [Group G] [Finite G]

theorem r847E3SU3G4RankTwo_dataOfSetup
    (hS : Standing G) (S : Setup G) :
    R847E3SU3G4RankTwo (dataOfSetup hS S) := by
  intro hsig Y hY hYN n hYn hn X hXY q hq hq2 hqn hXq hr hZ
  have h3 : 3 ∈ (dataOfSetup hS S).sig := by rw [hsig]; exact Set.mem_singleton 3
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) h3
  have hOp : F10.OpRes 3 S.M = S.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 hS.simple hS.nonab Nat.prime_three hsp
  have hMr : CFSG.Open.pRank 3 S.M = 3 := le_antisymm
    (pRank_le_three_dataOfSetup hS S Nat.prime_three (by norm_num) le_rfl) (hSg.three_le 3 h3)
  have hMY : S.M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hY.1.le).1 hYN
  obtain ⟨-, F, _, _, hF, ⟨ε⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hYn.2 (by decide)
  let hK : PiField false 2 n F := ⟨Nat.prime_two, by omega, hF⟩
  have hqsize : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num : 2 < 2 ^ 3)
    (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ n))
  let hu : UnitaryFieldData 2 n F := hK.unitary
  let ε' : Bar2 Y ⧸ center (Bar2 Y) ≃* unitaryPSU hu 3 :=
    ε.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm
  obtain ⟨β⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary.exists_mulEquiv_unitarySU_three
    hu hqsize hYn.1.1 ε' hZ
  let e : Bar2 Y ≃* slPi false 3 (2 ^ n) F :=
    β.symm.trans (slPiFalseEquiv 2 n F).symm
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := hu.charP
  have hqrSU : CFSG.Open.pRank q (⊤ : Subgroup (unitarySU 2 n F 3)) ≤ 1 := by
    apply CFSG.SectionRank.pRank_le hq.one_lt
    intro E _ hE
    rw [pow_one]
    exact UCK.card_le_of_sylow_isCyclic (fun P =>
      CFSG.ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow hF hq2 hq2
        (uc22ine229_not_dvd_two_pow_add_one hq hq2 hqn) P) hE
  have hqr : CFSG.Open.pRank q Y ≤ 1 := (uc22ine229_pRank_le_bar Y hq hq2).trans (by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt β]
    exact hqrSU)
  have hmod : ModThree false (2 ^ n) := by
    have h9 := UCK.nine_dvd_two_pow_add_one n (Nat.odd_iff.2 (by omega)) (by omega)
    have h3dvd : 3 ∣ 2 ^ n + 1 := (by norm_num : 3 ∣ 9).trans h9
    change 2 ^ n % 3 = 2
    omega
  have htwo := R847E3.two_le_pRank_normalizer_of_bar_su3 hY.1.le hMY hOp hMr hK hmod hqsize e
    hXY hq hq2 hqn hXq hqr
  omega


end CFSG.LocalAnalysis.UniquenessCase.UC22

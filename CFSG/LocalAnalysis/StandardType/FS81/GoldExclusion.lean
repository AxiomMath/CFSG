module

public import CFSG.LocalAnalysis.StandardType.FS81.GoldSharedSylow
public import CFSG.Goldschmidt.Final
import CFSG.LocalAnalysis.StandardType.FS81.GoldLayerSylow
import CFSG.LocalAnalysis.StandardType.FS81.GoldExclusionOdd
import CFSG.LocalAnalysis.StandardType.FS81.GoldExclusionTr
import CFSG.LocalAnalysis.StandardType.FS81.GoldExclusionCase
import CFSG.Goldschmidt.OddCore
import CFSG.Goldschmidt.Setup
import CFSG.Goldschmidt.StrongClosure
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate110
public import Certificates.Certificate117
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate5
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate6
public import Certificates.Certificate68
public import Certificates.Certificate7
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate72
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Goldschmidt

theorem goldExclusionSylow_of_certificates :
    GoldExclusionSylow := by
  have hcore : CoreStatement := coreStatement
  intro X _ _ hX P A hAP hAc hcl
  set M : Subgroup X := Subgroup.normalClosure (A : Set X) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  obtain ⟨Pm, hPmap⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hMn.isSubnormal
  have hPm : (Pm : Subgroup M) = (P : Subgroup X).subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hPmap, Subgroup.subgroupOf_map_subtype]
  have hAP' : A.subgroupOf M ≤ (Pm : Subgroup M) := by
    rw [hPm]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hAP (Subgroup.mem_subgroupOf.1 hx))
  have hcl' := stronglyClosed_subgroupOf P hcl hAM Pm hAP'
  have htop := normalClosure_subgroupOf_eq_top P hAP hcl (M := M) rfl
  have hab' := isMulCommutative_subgroupOf hAc M
  have hO := goldschmidtOddCore_eq_bot_of_normal hX hMn
  have hC : CoreConclusion M Pm (A.subgroupOf M) :=
    hcore M Pm (A.subgroupOf M) hAP' hab' hcl' htop hO
  by_cases hL : goldschmidtLayer M = ⊥
  · left
    exact normal_of_subgroupOf_eq_top hMn hAM (eq_top_of_layer_eq_bot hC hL)
  · right
    obtain ⟨hn1, hn2⟩ :=
      goldLayer_normalizer hcore Pm (A.subgroupOf M) hAP' hab' hcl' htop hO hC hL
    exact goldExclusionSylow_layer_case hMn hAM hAP hcl Pm hPm hn1 hn2

end CFSG.StandardType.FrameRoute.FS81

end

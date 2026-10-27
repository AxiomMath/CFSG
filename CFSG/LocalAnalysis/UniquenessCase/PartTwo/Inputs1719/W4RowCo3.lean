module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHeis
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem w4Thm11_1RowM_Co3_holds :
    W4Thm11_1RowM .Co3 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e⟩ := hs
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e co3_autInner
  show 8 ≤ E3.mParam Y
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Group.IsPerfect ↥L := hq.1
  have hkt : CFSG.AGLEmbedding.KernelTrivialAt (NativeSporadic.Carrier .Co3) 5 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.kernelTrivialAt_carrier_of_sporadicKernelTrivial
      CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_co3_five
  have hZ : ¬ 5 ∣ Nat.card (Subgroup.center ↥L) := not_dvd_card_center_of_kernelTrivialAt hkt e
  have hcard : Nat.card (NativeSporadic.Carrier .Co3) = 495766656000 :=
    CFSG.Sporadic.Schreier.Co3.card_Co3_of_perm
  have h2S : 2 ∣ Nat.card (NativeSporadic.Carrier .Co3) := by
    rw [hcard]
    norm_num
  exact W4Row.le_mParam_of_heisCfg hW hLY hO2 (fun t ht _ => hYL.le ht) e h2S (p := 5) (n := 0)
    (by norm_num) hZ (by rw [orderOf_two_zmod_five_co3]; norm_num) co3_heisGen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

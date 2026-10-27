module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusNatAparamHolds
public import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem k146Om6mA_holds : K146Om6mA := by
  intro U _ _ hU N S n hSN hSnorm hn hNat
  haveI : (S.subgroupOf N).Normal := hSnorm
  have hNle : N ≤ Subgroup.normalizer (S : Set (MulAut U)) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hSN
  have hbound : E3.aParam N ≤ 2 * n := by
    refine CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty N (2 * n) (fun A hA => ?_)
    have h :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.le_two_mul_of_mem_aSet_natOmegaMinus
        hNat hNle hA
    omega
  exact ⟨by omega, fun _ => hbound⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

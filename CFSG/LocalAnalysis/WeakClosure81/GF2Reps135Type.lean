module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGenericCatalog
import CFSG.HardMathSupport.Solomon.Proving.LBLemma27
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w135_typePartition (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (h : Is135Context Y L) :
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TypePartition
      (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨hK, -, hLY, -, hq, -⟩ := h
  have hKL : CFSG.IsKGroup ↥L :=
    CFSG.IsKGroup.of_injective hK (Subgroup.inclusion hLY) (Subgroup.inclusion_injective hLY)
  have hqo : CFSG.Open.IsQuasisimple ↥L := by
    refine ⟨?_, hq.2.1⟩
    have hperf := hq.1
    rw [Group.isPerfect_def, _root_.commutator_def] at hperf
    exact hperf
  exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.quasisimple_kgroup_type_of_bridge
    hbridge hqo (CFSG.HardMathSupport.Solomon.Proving.isKGroup_open_of_catalog hKL)

end CFSG.LocalAnalysis.WeakClosure81

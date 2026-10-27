module

public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
import CFSG.LocalAnalysis.UniquenessCase.UC22S206r
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.H13.A7BlkAct
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptCore ptCore_le_ptPre ptPre)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G]

theorem uc22s206t_outSolvable [Finite G] (D : Data G)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    {J : Subgroup (Bar2 D.M)} (hJ : IsComponentOf J ⊤) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (J ⧸ Subgroup.center J)) := by
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  exact hSch _ (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥J
    hJ.2.2) (uc22s206r_isCatalogGroup D hJ)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

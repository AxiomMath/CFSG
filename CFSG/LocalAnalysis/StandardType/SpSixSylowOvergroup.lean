module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalMax
public import Certificates.Certificate465002
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Quasithin.H13.L32NKGSp6Group
public import CFSG.Quasithin.Recognition.RuTypeDefs
public import Certificates.Certificate9442

public section

namespace CFSG.StandardType.SpSixSylow

open CFSG.KGroups.Sp6 CFSG.Quasithin.G2U CFSG.AGLEmbedding.KFactProofs.Sp62Local
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem eq_top_of_not_mem_W0
    {g : H6} (hg : g ∉ W0) :
    T0 ⊔ Subgroup.zpowers g = ⊤ :=
  eq_top_of_mem_not_mem (Certificates.certificate465002 g hg)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers g)) hg

theorem le_W0_of_ne_top
    {Y : Subgroup H6}
    (hT : T0 ≤ Y) (hY : Y ≠ ⊤) : Y ≤ W0 := by
  intro g hg
  by_contra hgW
  refine hY (eq_top_iff.2 ?_)
  rw [← eq_top_of_not_mem_W0 hgW]
  exact sup_le hT ((Subgroup.zpowers_le).2 hg)

end CFSG.StandardType.SpSixSylow

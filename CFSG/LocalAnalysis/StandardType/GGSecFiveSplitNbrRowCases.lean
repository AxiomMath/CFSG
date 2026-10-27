module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowCasesLab
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

theorem ggNbr_rowCases
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {K : Subgroup G}
    (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K) : GGInnerDiagOnLabel GGNSRowLab p Bs K := by
  obtain ⟨y, hnb⟩ := hK.1
  have hInnK : GGInnerDiagOn Bs K := hcfg.1.2.2.1.2 y K hnb
  have hHS := ggNbr_halfSplit_of_hyp ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))
    hcfg.1.1 hnb hInnK
  obtain ⟨lab, hlab, hhas, _, _, _, _, _, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
  have hmark := ggInnerDiagOn_relabel ggLabelRigidInput_holds hInnK hlab hhas
  refine largeEvenMarking_mono (fun lab' _ _ _ _ _ hP' => ⟨?_, hP'.2⟩) hmark
  rw [hP'.1]
  exact ggNSRowLab_of_halfSplit hlab hHSlab

end CFSG.StandardType

end

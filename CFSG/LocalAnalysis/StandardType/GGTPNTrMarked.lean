module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking
public import CFSG.LocalAnalysis.StandardType.GGNbrPrimeFieldExcl
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentJLevel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTPNTrMarked_of (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) : GGTPNTrMarked := by
  intro G _ _ p B Bs x L D J y K hc hL hK hn hN
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hc.1.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hc.2.1.1 hc.1.2.2.2.2.2.2.1.2.1
  have h5 : GGNbrClauseFiveMarking p x K :=
    (hc.1.2.2.2.2.2.2.2.2.2.1 y K ⟨hn.1, D, J, hc.2.2, hn.2⟩).2
  have hhalf : LargeEvenMarking ↥K fun lab _ _ _ _ _ =>
      LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥) := by
    rcases largeEvenMarking_or h5 with hh | hh
    · exact hh
    · exact absurd hh (ggNbr_not_primeField hraw hiso hp hp2 hxBs hK)
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hH⟩ := largeEvenMarking_exists_hasLabel hhalf
  have hmark := ggInnerDiagOn_relabel hRig hK hlab hhas
  refine largeEvenMarking_mono ?_ hmark
  rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
  subst h1
  exact ⟨trivial, hH, ggInducedInn_of_clause3 hN θ' h3⟩

theorem ggTPNTrMarked_holds
    : GGTPNTrMarked :=
  ggTPNTrMarked_of ggLabelRigidInput_holds ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))

end CFSG.StandardType

end

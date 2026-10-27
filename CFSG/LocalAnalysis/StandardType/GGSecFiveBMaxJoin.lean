module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveBEqualJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPosition
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperJoinCoord
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperJoinPerm
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem bProperMaxJoin_of_inputs (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hRoot : GGSecFiveBProperRootInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixB M)
    (hK : ∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K := by
  obtain ⟨n, e', hn, rfl⟩ := hM
  obtain ⟨-, eta, i0, hjoin, hLpos⟩ :=
    bOriginalPositionTheoryInput_holds hTBF hWI hX hTCJ hRig G p B Bs x L D J 𝒦 hR n hn
      (((CoxeterMatrix.B n).reindexGroupEquiv e').symm.trans e)
      (GGCoxeterPres.of_reindex_B (A := ggAutomizerJoin L Bs 𝒦) hn hP)
  have hF := hR.bProperFrame hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hB eta hjoin hK
  refine hR.ggG0_eq_of_forall_le fun y K hn' => ?_
  rcases hLpos with hLb | hLd | hLa
  · exact hF.le_join_of_bCoordinateBlock hLb hn'
  · exact hF.le_join_of_dCoordinateBlock hLd hn'
  · obtain ⟨i, j, hij, hroot⟩ := hRoot G p B Bs x L D J 𝒦 hR hB n eta hjoin hLa
    exact hF.le_join_of_aPermutationFull hLa hij hroot hn'

theorem bMaxJoinInput_of_inputs (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hRoot : GGSecFiveBProperRootInput) : BMaxJoinInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR ι M e hP hM hK
  by_cases hB : B = Bs
  · exact bEqualMaxJoinInput_of_inputs hTBF hWI hX hTCJ hRig hTPn hA8 hraw hiso hFC G p B Bs x
      L D J 𝒦 hR hB ι M e hP hM hK
  · exact bProperMaxJoin_of_inputs hTBF hWI hX hTCJ hRig hTPn hA8 hraw hiso hFC hRoot hR hB hP hM
      hK

end CFSG.StandardType

end

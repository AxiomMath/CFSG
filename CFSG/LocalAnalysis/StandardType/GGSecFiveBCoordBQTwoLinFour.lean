module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoLinDense
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseEndpoint

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggSecFiveBCoordBOffQTwoLinFourInput_of_inputs
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput) :
    GGSecFiveBCoordBOffQTwoLinFourInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n e hP hn eta i0 h𝒦 hL hLab hB hRM _ _ hdense
  exfalso
  subst hn
  obtain ⟨rfl, -⟩ := hLab.linQTwo_label
  obtain ⟨K, hK𝒦, hKL⟩ : ∃ K ∈ 𝒦, ¬ ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    by_contra hcon
    push Not at hcon
    have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs :=
      sup_le le_rfl (iSup₂_le fun K hK => hcon K hK)
    have hmem : SpCoord.sgnAut i0 ∈ bSignedFull 4 3 := Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩)
    rw [← h𝒦] at hmem
    have hmem' := Subgroup.map_mono hle hmem
    rw [hL] at hmem'
    exact sgnAut_not_mem_bCoordinateBlock Nat.prime_three (by norm_num) i0 hmem'
  obtain ⟨y, hyK⟩ := hR.2.2.2.1.2 K hK𝒦
  have hy : y ∈ Bs := hB ▸ hyK.1.2.1
  rcases hR.nbr_axis_or_dense hX hTCJ hRig hTPn hA8 hraw hiso hFC hB (by norm_num) eta h𝒦 hL hyK
      (hRM y K hyK) hKL hy with ⟨j, hj, hblk, hax⟩ | ⟨hδ, -⟩
  swap
  · exact hdense ⟨K, hK𝒦, hδ⟩
  obtain ⟨hKB, ⟨eLK⟩⟩ := ggSecFiveBCoordBSparseEndpointFourOn_holds
    (fun _ _ lab => lab.n = 1 ∧ lab.tag = .A) G 3 B Bs x L D J 𝒦 hR 4 e hP rfl eta i0 h𝒦 hL hLab
    hB hRM y hy K j hK𝒦 hyK hj hax hblk
  exact hR.false_of_qTwoLin_sparse (by norm_num) e hP eta hj h𝒦 hL hLab hK𝒦 eLK hKB

end CFSG.StandardType

end

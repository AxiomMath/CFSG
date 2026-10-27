module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperPos
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniJLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbrCell

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


theorem ggSecFiveBPermProperNbrInput_of_inputs (hTBF : GGTBFixInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput) (hLB : GGLBalanceInput)
    (hRoot : GGSecFiveBProperRootInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hI3 : GGNbrSubcomponentInput) (hPJ : GGStdSubPrimeInput)
    (hTE6R : GGTwE6ThreeNbrRankInput) : GGSecFiveBPermProperNbrInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ hn eta hJoin hAut _ _ _ hB hU
  obtain ⟨K, hK𝒦, i0, hKA⟩ := hR.exists_mem_bCoordinateBlock_of_ne hTBF hX hTCJ hRig hTPn hA8
    hraw hiso hFC hLB hRoot hB eta hJoin hAut hU
  obtain ⟨f, hf, hUf⟩ :=
    GGInnerDiagOnLabel.exists_n_eq_of_two_le (S := fun p lab => GGSecFiveBPermUniLabel n p lab) hU
  obtain ⟨a, a', haa', hroot⟩ := hRoot G p B Bs x L D J 𝒦 hR hB n eta hJoin hAut
  have hJ := hR.ggHasLabel_J_of_uniLabel hn (fun h => absurd h (by omega)) eta hAut hUf
    (Or.inr ⟨a, a', haa', hroot⟩) (fun h => absurd h (by omega))
  exact ⟨f, K, i0, hf, hR.uniCell_of_bCoordinateBlock hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ
    hTE6R hn eta hK𝒦 i0 hKA (by omega) (fun _ => hf) hUf hJ⟩

end CFSG.StandardType

end

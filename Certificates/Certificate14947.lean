module

public import CFSG.RankThree.PartOne.SEITZQ1.WordInputs
import Certificates.Kernel.Q1Words.Checks
import CFSG.Certificates.Kernel.OmegaPackedSound
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Ree.OmegaWordCheck

public section

open CFSG.Certificates.Kernel Certificates.Kernel.Q1Words

namespace Certificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne.SEITZQ1 in
theorem certificate14947 : omegaCheck Tag.F4 (q1Full false false) (q1Target false) = true ∧
    omegaCheck Tag.F4 (q1Full true false) (q1Target false) = true ∧
    omegaCheck Tag.F4 (q1Full false true) (q1Target true) = true ∧
    omegaCheck Tag.F4 (q1Full true true) (q1Target true) = true :=
  ⟨omegaCheck_of_omegaCheckP check_nz2_even, omegaCheck_of_omegaCheckP check_nz2_odd,
    omegaCheck_of_omegaCheckP check_b10_even, omegaCheck_of_omegaCheckP check_b10_odd⟩

end Certificates

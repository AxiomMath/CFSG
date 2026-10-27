module

public import CFSG.LocalAnalysis.StandardType.GGQTwoEndpoint
public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockProd
public import CFSG.LocalAnalysis.StandardType.GGQTwoRMGen
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanAQTwoBDefs
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan


theorem ggSecFiveDataResPhanAQTwoBInput_of_bs
    (hBS : BSCompletion) (hEn : GGSecFiveNSEnnolaInput) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hTCJ : GGTCJKnown) (hZS : ZS.UseInput) :
    GGSecFiveDataResPhanAQTwoBInput := fun hQ2 =>
  ggSecFiveDataResPhanAQTwoInput_of_inputs (K := GaloisField 2 2)
    (by simpa using GaloisField.card 2 2 (by norm_num)) hBS
    (qTwoRMGen_holds hEn hLB hPJ hTCJ hZS)
    (qTwoBlock_holds hEn hLB hPJ hTCJ hZS hQ2 (GaloisField 2 2))

end CFSG.StandardType.QTwo

end

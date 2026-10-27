module

public import CFSG.Sporadic.Co1.Cover.Data
public import CFSG.Sporadic.Co1Block.TwoACheckInputs
public import Certificates.Data.CFSGNative.Co1K105.Check
public import Certificates.Data.Kernel.Co1K105.Defs
public import Certificates.Data.Kernel.Co1K105.LettersCheck
public import Certificates.Data.Kernel.SporLatDc2Check
import Certificates.Kernel.Co1K105.Final
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Co1K105.LettersGlue
public import CFSG.Sporadic.Co1.Module.InvDataBase
public import CFSG.Sporadic.Co1.Module.InvRepsBase

public section

namespace Certificates

theorem certificate10507 :
    CFSG.KD.Co1K105.co1KLettersCheck (CFSG.Sporadic.Co1.Cover.rrCov 0)
        (CFSG.Sporadic.Co1.Cover.rrCov 4) (CFSG.Sporadic.Co1.Cover.rrCov 5)
        CFSG.Sporadic.Co1Block.iotaARows CFSG.Sporadic.Co1.Cover.epsRows
        CFSG.Sporadic.Co1Block.twoAQRows
        (CFSG.Sporadic.Co1Block.Native.brayElts
          (CFSG.Sporadic.Co1Block.Native.brayRows CFSG.Sporadic.Co1Block.iotaARows
            CFSG.Sporadic.Co1Block.twoAD1) CFSG.Sporadic.Co1Block.twoABray)
        (CFSG.KD.Co1K105.t24Codes.map fun c => CFSG.KD.Co1K105.wordOf c.1 c.2)
        CFSG.KD.Co1K105.L = true ∧
      CFSG.KC.SLD2.dc2Check CFSG.KD.Co1K105.C CFSG.KD.Co1K105.D = true :=
  ⟨CFSG.KD.Co1K105.letters_k, CFSG.KD.Co1K105.dc2_ok⟩

end Certificates

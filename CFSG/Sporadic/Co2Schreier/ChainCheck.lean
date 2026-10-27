
module

public import CFSG.Sporadic.Co2Schreier.ChainCheckBase

public import CFSG.Sporadic.Co2Schreier.Arrays
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public import Certificates.Certificate2049

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu

theorem chainC_check : recordOK 2300 localRec.chains.C 4 = true ∧
    recordOrbits 2300 localRec.chains.C = [256, 1260, 18, 32, 2, 2] :=
  Certificates.certificate2049.1

theorem chainD_check : recordOK 2300 localRec.chains.D 4 = true ∧
    recordOrbits 2300 localRec.chains.D = [1920, 56, 96, 4] :=
  Certificates.certificate2049.2.1

theorem chainS_check : recordOK 2300 localRec.chains.S 4 = true ∧
    recordOrbits 2300 localRec.chains.S = [256, 256, 4] :=
  Certificates.certificate2049.2.2.1

theorem chainJoin_check : recordOK 2300 localRec.chains.join 4 = true ∧
    recordOrbits 2300 localRec.chains.join = [2300, 1408, 567, 192, 10, 12] :=
  Certificates.certificate2049.2.2.2.1

theorem words_check : wordsCheck localRec levelsS = true :=
  Certificates.certificate2049.2.2.2.2

end CFSG.Sporadic.Co2Schreier

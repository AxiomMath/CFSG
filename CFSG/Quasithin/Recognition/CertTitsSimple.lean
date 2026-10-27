
module

public import CFSG.Quasithin.Recognition.CertTitsBase

public import CFSG.Quasithin.Recognition.CertTits
public import CFSG.Quasithin.Recognition.CertPermSimple
public import CFSG.Quasithin.Recognition.CertDataTitsSimple
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Quasithin.Recognition.CertTits
public meta import CFSG.Quasithin.Recognition.CertPermSimple
public meta import CFSG.Quasithin.Recognition.CertDataTits
public meta import CFSG.Quasithin.Recognition.CertDataTitsSimple
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsSimpleInputs
public import Certificates.Certificate8077

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem titsPair_check :
    isInvA 1755 titsA (invCand 1755 titsA) = true ∧
    isInvA 1755 titsB (invCand 1755 titsB) = true ∧
    lettersOK titsGens.size (titsAbWords.getD 0 []) = true ∧
    lettersOK titsGens.size (titsAbWords.getD 1 []) = true ∧
    titsPairO.size ≤ titsPairStrong.size ∧
    (∀ i < titsPairO.size, titsPairStrong[i]! = titsPairO[i]!) ∧
    rawChainOK 1755 (titsPairStrong.extract 0 titsPairO.size) titsPairStrong
      (titsPairBase.map Fin.val).toArray titsPairRawWords 4 = true ∧
    rawOrbitSizes 1755 titsPairStrong (titsPairBase.map Fin.val).toArray =
      [1755, 10, 8, 2, 8, 4, 2] ∧
    primCheck 1755 titsPairStrong 0 titsLabels titsRoots 5 titsTw titsHw = true ∧
    eqA 1755 (powA 1755 titsA 2) (idA 1755) = true ∧ eqA 1755 titsA (idA 1755) = false ∧
    eqA 1755 (powA 1755 titsB 3) (idA 1755) = true ∧ eqA 1755 titsB (idA 1755) = false ∧
    eqA 1755 (powA 1755 (compA 1755 titsA titsB) 13) (idA 1755) = true ∧
    eqA 1755 (compA 1755 titsA titsB) (idA 1755) = false :=
  Certificates.certificate8077.1

theorem tits_labelsDivisorOK :
    LabelsDivisorOK 1755 5 (by norm_num) titsLabels ⟨0, by norm_num⟩ :=
  Certificates.certificate8077.2

end CFSG.Quasithin

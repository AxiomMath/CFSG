
module

public import Certificates.Certificate2213Base

public import CFSG.Sporadic.Schreier.ONCheckLocalInputs
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public meta import CFSG.Sporadic.Schreier.ONOuterData
import Certificates.Kernel.Sporadic.ON4.Final
import Certificates.Data.CFSGNative.ON.Certificate

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native in
theorem certificate2213 : (localChainOK (CFSG.ONSchreier.wordArrs Data.TWords) Data.TChain = true)
    ∧ (localChainOK (CFSG.ONSchreier.wordArrs Data.MWords) Data.MChain = true)
    ∧ (localChainOK (CFSG.ONSchreier.wordArrs Data.LWords) Data.LChain = true)
    ∧ (localChainOK (commGens nPts (CFSG.ONSchreier.wordArrs Data.MWords) Data.MCommutatorSpecs) Data.McommChain =
      true
    )
    ∧ (localChainOK (commGens nPts (CFSG.ONSchreier.wordArrs Data.LWords) Data.LCommutatorSpecs) Data.LcommChain =
      true
    )
    ∧ (localChainOK jointArrs Data.jointChain = true)
    ∧ (allBelowN 3 (fun j => pisInv nPts (CFSG.ONSchreier.wordArrs Data.MWords)[j]!
        (pinvCand nPts (CFSG.ONSchreier.wordArrs Data.MWords)[j]!)) = true ∧
      allBelowN 2 (fun j => pisInv nPts (CFSG.ONSchreier.wordArrs Data.LWords)[j]!
        (pinvCand nPts (CFSG.ONSchreier.wordArrs Data.LWords)[j]!)) = true ∧
      pisInv nPts (wordArr Data.pairConjugatorWord)
        (pinvCand nPts (wordArr Data.pairConjugatorWord)) = true
    ) := KernelSpor.ON4K.facts2213

end Certificates

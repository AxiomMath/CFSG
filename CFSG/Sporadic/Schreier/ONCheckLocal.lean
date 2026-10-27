
module

public import CFSG.Sporadic.Schreier.ONCheckLocalBase

public import CFSG.Sporadic.Schreier.ONCheckChain
public import CFSG.Sporadic.Schreier.ONOuterData
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public meta import CFSG.Sporadic.Schreier.ONOuterData
public import CFSG.Sporadic.Schreier.ONCheckLocalInputs
public import Certificates.Certificate2213

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

theorem t_chain_cert : localChainOK (wordArrs Data.TWords) Data.TChain = true :=
  Certificates.certificate2213.1

theorem m_chain_cert : localChainOK (wordArrs Data.MWords) Data.MChain = true :=
  Certificates.certificate2213.2.1

theorem l_chain_cert : localChainOK (wordArrs Data.LWords) Data.LChain = true :=
  Certificates.certificate2213.2.2.1

theorem mcomm_chain_cert :
    localChainOK (commGens nPts (wordArrs Data.MWords) Data.MCommutatorSpecs) Data.McommChain =
      true :=
  Certificates.certificate2213.2.2.2.1

theorem lcomm_chain_cert :
    localChainOK (commGens nPts (wordArrs Data.LWords) Data.LCommutatorSpecs) Data.LcommChain =
      true :=
  Certificates.certificate2213.2.2.2.2.1

theorem joint_chain_cert : localChainOK jointArrs Data.jointChain = true :=
  Certificates.certificate2213.2.2.2.2.2.1

theorem seed_invs_cert :
    allBelowN 3 (fun j => pisInv nPts (wordArrs Data.MWords)[j]!
      (pinvCand nPts (wordArrs Data.MWords)[j]!)) = true ∧
    allBelowN 2 (fun j => pisInv nPts (wordArrs Data.LWords)[j]!
      (pinvCand nPts (wordArrs Data.LWords)[j]!)) = true ∧
    pisInv nPts (wordArr Data.pairConjugatorWord)
      (pinvCand nPts (wordArr Data.pairConjugatorWord)) = true :=
  Certificates.certificate2213.2.2.2.2.2.2

end CFSG.ONSchreier

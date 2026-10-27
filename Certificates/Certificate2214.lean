module

public import CFSG.Sporadic.Schreier.ONCheckR3EInputs
public meta import CFSG.Sporadic.Schreier.ONCheckAux
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
import Certificates.Kernel.Sporadic.ON8.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.PSL3Four.Native in
theorem certificate2214 : (dConj.all (fun g => g.size == nPts) = true ∧ enumOK nPts dConj dEnum = true ∧
      dEnum.tabs.size = 144 ∧ aTabs.size = 4 ∧
      hGensArr.all (fun g => g.size == nPts) = true ∧ enumOK nPts hGensArr hEnum = true ∧
      hEnum.tabs.size = 144 ∧
      hGensArr.all (fun g => aTabs.all fun a => comp nPts g a == comp nPts a g) = true ∧
      hEnum.tabs.all (fun c => c == pid nPts || c == hvhvArr || order7Moves c) = true
    )
    ∧ (allBelowN 5 (fun j => pisInv nPts dhGens[j]! dhInv[j]!) = true ∧
      allBelowN 3 (fun j => plettersOK 5 mWordsDH[j]! &&
        peq nPts (pword nPts dhGens dhInv mWordsDH[j]!) (wordArrs Data.MWords)[j]!) = true ∧
      hWordsDH.all (plettersOK 5) = true ∧
      peq nPts (Nat.repeat (pcomp nPts hArr) 7 (pid nPts)) (pid nPts) = true ∧
      memIn MStrong Data.MChain.base vArr = true ∧
      peq nPts (pcomp nPts vArr vArr) (pid nPts) = true ∧
      peq nPts vArr (pid nPts) = false ∧ peq nPts vArr zArr = false ∧
      allBelowN 4 (fun j => peq nPts (pcomp nPts vArr dConj[j]!) (pcomp nPts dConj[j]! vArr)) =
        true ∧
      peq nPts (pcomp nPts vArr hArr) (pcomp nPts hArr vArr) = false ∧
      peq nPts zArr (qPowArr 2) = true ∧
      (#[1, 3] : Array Nat).all (fun k => !(allBelowN 3 fun j =>
        peq nPts (pcomp nPts (qPowArr k) (wordArrs Data.MWords)[j]!)
          (pcomp nPts (wordArrs Data.MWords)[j]! (qPowArr k)))) = true ∧
      (#[1, 3] : Array Nat).all (fun k => !(allBelowN 4 fun j =>
        peq nPts (pcomp nPts (qPowArr k) dConj[j]!) (pcomp nPts dConj[j]! (qPowArr k)))) = true ∧
      (#[1, 3] : Array Nat).all (fun k => !(aTabs.all fun a =>
        peq nPts (pcomp nPts (qPowArr k) a) (pcomp nPts a (qPowArr k)))) = true
    )
    ∧ (aTabs.all (fun a => blockImgOK a Data.quotientBlocks (bTab a)) = true ∧
      (m120Enum.tabs.filter fun x => aTabs.all fun a =>
        comp 120 x (bTab a) == comp 120 (bTab a) x).size = 144 ∧
      plettersOK 5 liftWordDH = true ∧
      blockImgOK mLiftArr Data.quotientBlocks (bTab mLiftArr) = true ∧
      aTabs.all (fun a => comp 120 (bTab mLiftArr) (bTab a) == comp 120 (bTab a) (bTab mLiftArr)) =
        true ∧
      allBelowN 4 (fun k => !(aTabs.all fun a =>
        peq nPts (pcomp nPts (pcomp nPts mLiftArr (qPowArr k)) a)
          (pcomp nPts a (pcomp nPts mLiftArr (qPowArr k))))) = true
    )
    ∧ (pisInv nPts vArr (pinvCand nPts vArr) = true) := KernelSpor.ON8.facts2214

end Certificates

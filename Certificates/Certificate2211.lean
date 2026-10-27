module

public import CFSG.Sporadic.Schreier.ONCheckAuxInputs
public meta import CFSG.Sporadic.Schreier.ONCheckLocal
public meta import CFSG.Sporadic.Schreier.ONGlue
import Certificates.Kernel.Sporadic.ON3.Final
import Certificates.Kernel.Sporadic.ON3.UProved

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native in
theorem certificate2211 : (peq nPts (pcomp nPts zArr zArr) (pid nPts) = true ∧ peq nPts zArr (pid nPts) = false ∧
      memIn TStrong Data.TChain.base zArr = true ∧ fixCount nPts zArr = 240 ∧ zArr[0]! = 0 ∧
      allBelowN 3 (fun j => peq nPts (pcomp nPts (wordArrs Data.MWords)[j]! zArr)
        (pcomp nPts zArr (wordArrs Data.MWords)[j]!)) = true
    )
    ∧ (commCount (cLevels nPts Data.baseList.toArray
        (allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray))
      (allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray) 1 2 zArr
      #[0, 227759, 100817] = 672
    )
    ∧ (pointsOK nPts Data.TPoints rPos = true ∧
      allBelowN 6 (fun j => restrictOK (wordArrs Data.TWords)[j]! Data.TPoints
        (rTab (wordArrs Data.TWords)[j]!)) = true ∧
      restrictOK zArr Data.TPoints Data.T32z = true ∧
      coversOK 32 ((wordArrs Data.TWords).map rTab) Data.T32Chain.generators = true ∧
      coversOK 32 Data.T32Chain.generators ((wordArrs Data.TWords).map rTab) = true
    )
    ∧ (blocksOK nPts Data.quotientBlocks bPos = true ∧
      allBelowN 3 (fun j => blockImgOK (wordArrs Data.MWords)[j]! Data.quotientBlocks
        (bTab (wordArrs Data.MWords)[j]!)) = true ∧
      allBelowN 2 (fun j => blockImgOK (wordArrs Data.LWords)[j]! Data.quotientBlocks
        (bTab (wordArrs Data.LWords)[j]!)) = true ∧
      coversOK 120 ((wordArrs Data.MWords).map bTab) Data.M120Chain.generators = true ∧
      coversOK 120 Data.M120Chain.generators ((wordArrs Data.MWords).map bTab) = true ∧
      coversOK 120 ((wordArrs Data.LWords).map bTab) Data.L120Chain.generators = true ∧
      coversOK 120 Data.L120Chain.generators ((wordArrs Data.LWords).map bTab) = true ∧
      blockImgOK qArr Data.quotientBlocks (pid 120) = true
    )
    ∧ (memIn LStrong Data.LChain.base qArr = true ∧
      peq nPts (pcomp nPts qArr (pcomp nPts qArr (pcomp nPts qArr qArr))) (pid nPts) = true ∧
      peq nPts (pcomp nPts qArr qArr) (pid nPts) = false ∧
      allBelowN 2 (fun j => peq nPts (pcomp nPts (wordArrs Data.LWords)[j]! qArr)
        (pcomp nPts qArr (wordArrs Data.LWords)[j]!)) = true ∧
      memIn MStrong Data.MChain.base tArr = true ∧
      peq nPts tArr (pcomp nPts cArr (pcomp nPts zArr (pinvCand nPts cArr))) = true ∧
      peq nPts tArr zArr = false ∧
      allBelowN 2 (fun j => memIn MStrong Data.MChain.base (wordArrs Data.LWords)[j]!) = true
    )
    ∧ (allBelowN 4 (fun j => memIn MStrong Data.MChain.base
      (wordArrs Data.intersectionWords)[j]!) = true ∧
      allBelowN 4 (fun j => memIn MStrong Data.MChain.base dConj[j]!) = true ∧
      allBelowN 4 (fun j => blockImgOK dConj[j]! Data.quotientBlocks
        Data.D120Generators[j]!) = true ∧
      countBelowN 4 (fun k => allBelowN 4 fun j =>
        peq nPts (pcomp nPts (cqcArr k) (wordArrs Data.intersectionWords)[j]!)
          (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr k))) = 2
    )
    ∧ (pisInv 120 Data.quotientConjugator (pinvCand 120 Data.quotientConjugator) = true ∧
      allBelowN 2 (fun j => memFull 120
        (cLevels 120 Data.PSL120Chain.base (allSteps Data.PSL120Chain.strongGenerators
          (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base))
        (allInvSteps Data.PSL120Chain.strongGenerators
          (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base)
        Data.PSL120Chain.base (pcomp 120 Data.quotientConjugator
          (pcomp 120 (bTab (wordArrs Data.LWords)[j]!)
            (pinvCand 120 Data.quotientConjugator)))) = true
    ) :=
  ⟨KernelSpor.ON3.z_part, KernelSpor.ON3.comm_part, KernelSpor.ON3.r_facts,
    KernelSpor.ON3.block_facts, KernelSpor.ON3.qt_part, KernelSpor.ON3.d0_part,
    KernelSpor.ON3.u_facts_proved⟩

end Certificates

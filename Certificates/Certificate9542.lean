module

public import Certificates.Data.Item434D42
import Certificates.Kernel.D4.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne in
theorem certificate9542 :
    (caseChainOK2P 2457 d4ChainAArrs d4ChainABaseArr d4ChainAWords d4GenA d4GenB = true ∧
      rawOrbitSizes 2457 d4ChainAArrs d4ChainABaseArr = [2457, 2048, 7, 1, 1, 3, 2]) ∧
    (linesOK3 3 81 31 2457 d4QGens d4Keys d4QCert d4Lines = true ∧
      allLt d4QGens.size (fun l => siftA 2457 d4LevelsA d4ChainABaseArr 0 d4QGens[l]!) = true ∧
      transOK2 31 2457 d4Trans d4Lines d4Lines d4Rec d4LevelsA d4ChainABaseArr = true ∧
      allLt 31 (fun j => decide (d4Rec.getD j 0 < 2)) = true) ∧
    (centOKP 3 2457 d4ChainAArrs d4ChainABaseArr d4Lines[0]! d4RelsA d4CAGens d4Keys d4CACert
      1512 = true) :=
  ⟨⟨KernelD4.chainA_ok, KernelD4.orbitsA⟩,
    ⟨KernelD4.lines_ok, KernelD4.siftQ_ok, KernelD4.trans_ok, KernelD4.rec_ok⟩,
    KernelD4.caseA_ok⟩

end Certificates

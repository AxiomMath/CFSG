module

public import Certificates.Data.K426McL
import Certificates.Kernel.K426.McLFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
theorem certificate8057 :
    (linesOK3 3 729 148 275 mcl3QGens mcl3Keys mcl3QCert mcl3Lines = true ∧
      allLt mcl3QGens.size (fun l => siftA 275 PairMcL.levels PairMcL.baseArr 0 mcl3QGens[l]!) =
        true ∧
      transOK2 148 275 mcl3Trans mcl3Lines mcl3Lines mcl3Rec PairMcL.levels PairMcL.baseArr =
        true ∧
      allLt 148 (fun j => decide (mcl3Rec.getD j 0 < 2)) = true) ∧
    (caseChainOK2P 275 mcl3ChainAArrs mcl3ChainABaseArr mcl3ChainAWords mclStrongArrs[0]!
        mclStrongArrs[1]! = true ∧
      centOKP 3 275 mcl3ChainAArrs mcl3ChainABaseArr mcl3Lines[0]! mcl3RelsA mcl3CAGens
        mcl3Keys mcl3CACert 29160 = true ∧
      normalOKP 3 275 mcl3CAGens mcl3OGens mcl3Keys mcl3CACert mcl3OCert 243 PairMcL.levels
        PairMcL.baseArr = true) ∧
    (caseChainOK2P 275 mcl3ChainBArrs mcl3ChainBBaseArr mcl3ChainBWords mclStrongArrs[0]!
        mclStrongArrs[1]! = true ∧
      centOKP 3 275 mcl3ChainBArrs mcl3ChainBBaseArr mcl3Lines[1]! mcl3RelsB mcl3CBGens
        mcl3Keys mcl3CBCert 972 = true) := KernelK426.facts

end Certificates

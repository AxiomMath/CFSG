module

public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
import Certificates.Kernel.HeLoc.FiveDFacts
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB in
theorem certificate10051 :
    (linesOKG 5 25 6 8330 heFiveQGens heFiveKeys heFiveQCert heFiveLines = true ∧
      allLt heFiveQGens.size (fun l => siftA 8330 heLevels heBase.toArray 0 heFiveQGens[l]!) =
        true ∧
      transOKG 6 8330 heFiveTransporters heFiveLines heFiveRec heFiveRLevels heFiveCase0BaseArr =
        true ∧
      allLt 6 (fun j => (List.range 1).any fun i => heFiveRec.getD j 0 == i) = true ∧
      heFiveRec.getD 0 0 = 0)
    ∧ (caseChainOK3 8330 heFiveCase0Arrs heFiveCase0BaseArr heFiveCase0Words (heGen 0) (heGen 1)
        heUArr = true ∧
      centOKP 5 8330 heFiveCase0Arrs heFiveCase0BaseArr heFiveLines[0]! heFiveCase0Rels
        heFiveC0Gens heFiveKeys heFiveC0Cert 600 = true ∧
      eqA 8330 heFiveC0Gens[0]! heFiveLines[0]! = true ∧
      derivedOKP 5 60 8330 heFiveC0Gens heFiveDGens0 heFiveKeys heFiveC0Cert heFiveDCert0
        heFiveDWit0[0]! heFiveDWit0[1]! heFiveLines[0]! heLevels heBase.toArray = true) := KernelHeLoc.FiveL.facts

end Certificates

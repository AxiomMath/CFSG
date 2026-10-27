module

public import Certificates.Data.ONanG28T
import Certificates.Kernel.CertF8.Glue9557

public section

namespace Certificates

open CFSG.AGLEmbedding.KFactProofs.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28 in
theorem certificate9557 : CFSG.RankThree.PartTwo.Sec4.Item434G28.t3OK txL = true ∧ frobStable txL = true ∧
    centerOK txL tGens tzc = true ∧ zOKc txL tzc tGens = true ∧ aOK txL tU tZ = true ∧
    omegaOK tU tZ = true ∧ compOK txL tU tZ = true ∧ qOK txL tzc tB1 tY1 = true ∧
    qOK txL tzc tB2 tY2 = true ∧ gOK tzc txL[tB1]! txL[tB2]! gW = true := Kernel.CertF8.C9557.checks9557

end Certificates

module

public import Certificates.Data.J3Cls
import Certificates.Kernel.J3Ref.Facts

public section

open CFSG.SectionRank.QTK.Insp443.J3Cls
open CFSG.Sporadic.SmallOddCore (enumOK normOK centCount)
open CFSG.Sporadic.SmallOddCore.Native (memT mulClosureH)
open CFSG.Quasithin.KGC31.Native (ebasisOK masksOK)

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.QTK.Insp443.J3Cls in
open CFSG.Sporadic.SmallOddCore (enumOK normOK centCount) in
open CFSG.Sporadic.SmallOddCore.Native (memT mulClosureH) in
open CFSG.Quasithin.KGC31.Native (ebasisOK masksOK) in
theorem certificate589304 : tblsOK = true ∧ ebasisOK 6156 eB = true ∧
    masksOK 6156 eB CFSG.SectionRank.QTK.Insp443.J3Cls.omT [2, 3, 8, 12] = true ∧ masksOK 6156 eB (clsTbl 5) [3, 1, 10, 15] = true ∧
    masksOK 6156 eB (clsTbl 6) [10, 15, 3, 1] = true ∧
    enumOK 6156 3000 1920 CFSG.SectionRank.QTK.Insp443.J3Cls.cGens = true ∧ centCount 6156 3000 CFSG.SectionRank.QTK.Insp443.J3Cls.cGens eB = 16 ∧
    normCount = 192 ∧ enumOK 6156 3000 960 mGens = true ∧ enumOK 6156 3000 2880 CFSG.SectionRank.QTK.Insp443.J3Cls.nGens = true ∧
    CFSG.Sporadic.SmallOddCore.normOK 6156 3000 mGens [CFSG.SectionRank.QTK.Insp443.J3Cls.omT] = true ∧
    eB.all (memT 6156 (mulClosureH 6156 mGens.toArray 3000).1) = true ∧
    enumOK 6156 3000 128 sGens = true ∧ CFSG.SectionRank.QTK.Insp443.J3Cls.clsOK = true := KernelJ3Ref.facts589304

end Certificates

end

end

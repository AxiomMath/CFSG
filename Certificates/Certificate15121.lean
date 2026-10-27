module

public import CFSG.Sporadic.SuzRecog.MixedCellChecks
import Certificates.Kernel.Sporadic.OddCore.SuzMcF
import Certificates.Kernel.Sporadic.OddCore.SuzMcS00
import Certificates.Kernel.Sporadic.OddCore.SuzMcS01
import Certificates.Kernel.Sporadic.OddCore.SuzMcS02
import Certificates.Kernel.Sporadic.OddCore.SuzMcS03
import Certificates.Kernel.Sporadic.OddCore.SuzMcS04
import Certificates.Kernel.Sporadic.OddCore.SuzMcS05
import Certificates.Kernel.Sporadic.OddCore.SuzMcS06
import Certificates.Kernel.Sporadic.OddCore.SuzMcS07
import Certificates.Kernel.Sporadic.OddCore.SuzMcS08
import Certificates.Kernel.Sporadic.OddCore.SuzMcS09
import Certificates.Kernel.Sporadic.OddCore.SuzMcS10
import Certificates.Kernel.Sporadic.OddCore.SuzMcS11
import Certificates.Kernel.Sporadic.OddCore.SuzMcS12
import Certificates.Kernel.Sporadic.OddCore.SuzMcS13
import Certificates.Kernel.Sporadic.OddCore.SuzMcS14
import Certificates.Kernel.Sporadic.OddCore.SuzMcS15
import Certificates.Kernel.Sporadic.OddCore.SuzMcS16
import Certificates.Kernel.Sporadic.OddCore.SuzMcS17
import Certificates.Kernel.Sporadic.OddCore.SuzMcS18
import Certificates.Kernel.Sporadic.OddCore.SuzMcS19
import Certificates.Kernel.Sporadic.OddCore.SuzMcS20
import Certificates.Kernel.Sporadic.OddCore.SuzMcS21
import Certificates.Kernel.Sporadic.OddCore.SuzMcS22
import Certificates.Kernel.Sporadic.OddCore.SuzMcS23
import Certificates.Kernel.Sporadic.OddCore.SuzMcP00
import Certificates.Kernel.Sporadic.OddCore.SuzMcP01
import Certificates.Kernel.Sporadic.OddCore.SuzMcP02
import Certificates.Kernel.Sporadic.OddCore.SuzMcP03
import Certificates.Kernel.Sporadic.OddCore.SuzMcP04
import Certificates.Kernel.Sporadic.OddCore.SuzMcP05
import Certificates.Kernel.Sporadic.OddCore.SuzMcP06
import Certificates.Kernel.Sporadic.OddCore.SuzMcP07
import Certificates.Kernel.Sporadic.OddCore.SuzMcP08
import Certificates.Kernel.Sporadic.OddCore.SuzMcP09
import Certificates.Kernel.Sporadic.OddCore.SuzMcP10
import Certificates.Kernel.Sporadic.OddCore.SuzMcP11

public section

open CFSG

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate15121 : CFSG.Sporadic.SuzRecog.MixedCell.singleMem 0 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 1 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 2 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 3 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 4 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 5 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 6 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 7 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 8 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 9 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 10 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 11 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 12 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 13 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 14 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 15 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 16 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 17 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 18 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 19 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 20 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 21 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 22 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.singleMem 23 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 0 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 1 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 2 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 3 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 4 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 5 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 6 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 7 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 8 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 9 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 10 ∧
    CFSG.Sporadic.SuzRecog.MixedCell.pairMem 11 ∧
    CFSG.Sporadic.SuzRecog.MixedCellCheck.mcPermsOK = true ∧
    CFSG.Sporadic.SuzRecog.MixedCellCheck.mcMembersOK = true ∧
    CFSG.Sporadic.SuzRecog.MixedCellCheck.mcCommOK = true ∧
    CFSG.Sporadic.SuzRecog.MixedCellCheck.mcLettersOK = true ∧
    CFSG.Sporadic.SuzRecog.MixedCellCheck.mcRelsOK = true ∧
    CFSG.Sporadic.SuzRecog.MixedCellCheck.mcCellsOK = true ∧
    CFSG.Sporadic.SuzRecog.MixedCellCheck.mcBoundOK 0 = true ∧
    CFSG.Sporadic.SuzRecog.MixedCellCheck.mcBoundOK 2 = true ∧
    CFSG.Sporadic.SuzRecog.MixedCellCheck.mcRemarkOK = true := by
  exact ⟨SuzMcS00.mem, SuzMcS01.mem, SuzMcS02.mem, SuzMcS03.mem, SuzMcS04.mem, SuzMcS05.mem,
    SuzMcS06.mem, SuzMcS07.mem, SuzMcS08.mem, SuzMcS09.mem, SuzMcS10.mem, SuzMcS11.mem,
    SuzMcS12.mem, SuzMcS13.mem, SuzMcS14.mem, SuzMcS15.mem, SuzMcS16.mem, SuzMcS17.mem,
    SuzMcS18.mem, SuzMcS19.mem, SuzMcS20.mem, SuzMcS21.mem, SuzMcS22.mem, SuzMcS23.mem,
    SuzMcP00.mem, SuzMcP01.mem, SuzMcP02.mem, SuzMcP03.mem, SuzMcP04.mem, SuzMcP05.mem,
    SuzMcP06.mem, SuzMcP07.mem, SuzMcP08.mem, SuzMcP09.mem, SuzMcP10.mem, SuzMcP11.mem,
    SuzMcF.perms, SuzMcF.members, SuzMcF.comm, SuzMcF.letters, SuzMcF.rels, SuzMcF.cells,
    SuzMcF.bound0, SuzMcF.bound2, SuzMcF.remark⟩

end Certificates

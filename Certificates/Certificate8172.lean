module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
public import CFSG.RankThree.PartTwo.Toolkit.RawGL
public import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public import CFSG.RankThree.PartTwo.Toolkit.PermTab
public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.RankThree.PartTwo.Toolkit.BloomMonoStdInputs
import Certificates.Kernel.Misc.Perm.BloomMono

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Toolkit
  CFSG.RankThree.PartTwo.Toolkit.Raw Subgroup CFSG.RankThree.SubgroupLists in
open scoped Matrix in
theorem certificate8172 : monoCheck = true := KernelMisc.BloomMono.facts

end Certificates

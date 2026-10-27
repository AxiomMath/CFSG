module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
public import CFSG.RankThree.PartTwo.Toolkit.RawGL
public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.RankThree.PartTwo.Toolkit.Bloom13Inputs
import Certificates.Kernel.Misc.Perm.Bloom13

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Toolkit
  CFSG.RankThree.PartTwo.Toolkit.Raw Subgroup in
open scoped Matrix in
theorem certificate8171 : bloom13Check = true := KernelMisc.Bloom13.facts

end Certificates

module

public import Certificates.Kernel.Census.HSC.Data
import all Certificates.Kernel.Census.HSC.Data
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.HSC

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kPc : ppcOK 100 7 d.xs d.rs d.cjs d.bs = true := by quickRfl

theorem kInv : pinvOK 100 7 d.xs d.us d.im d.wt = true := by quickRfl

theorem kTab : ptabOK 100 7 d.xs d.cm d.cs d.ci = true := by quickRfl

theorem kRl : Nat.beq d.roots.length d.us.size = true := by quickRfl

theorem kLen : Nat.beq d.xs.length 10 = true := by quickRfl

theorem kNs : Nat.beq d.nodes.size 108 = true := by quickRfl

theorem kR : (d.us.toList.zip d.roots).all
    (fun ur => prootOKC 100 7 (d.nodes.map NodeP.basis) cN d.cs d.ci ur.1 ur.2) = true := by
  quickRfl

end CertificateChecks.KernelCensus.HSC

end

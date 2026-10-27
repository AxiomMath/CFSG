module

public import Certificates.Kernel.Census.HeC.K
import all Certificates.Kernel.Census.HeC.Data
import all Certificates.Kernel.Census.HeC.K
import all Certificates.Data.Kernel.Census.HeConj2
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.HeT.Tab
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CertificateChecks.KernelCensus.HeCj

open CFSG.KC.HeConj

set_option maxRecDepth 1000000

theorem kT : tree32OK 32 6 d = true := by quickRfl

theorem kB : bridgeOK nv CertificateChecks.KernelSporSch.HeTc.nfp uP bsH 8330 32 6 d = true := by
  quickRfl

theorem kLen : Nat.beq d.xs.length 11 = true := by quickRfl

theorem kNs : Nat.beq d.nb.size 130 = true := by quickRfl

end CertificateChecks.KernelCensus.HeCj

end

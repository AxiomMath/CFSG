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

theorem kN0 : nodes32OK 32 6 d (List.range' 0 26) = true := by quickRfl
theorem kN26 : nodes32OK 32 6 d (List.range' 26 26) = true := by quickRfl
theorem kN52 : nodes32OK 32 6 d (List.range' 52 26) = true := by quickRfl
theorem kN78 : nodes32OK 32 6 d (List.range' 78 26) = true := by quickRfl
theorem kN104 : nodes32OK 32 6 d (List.range' 104 26) = true := by quickRfl

end CertificateChecks.KernelCensus.HeCj

end

module

public import Certificates.Data.TabSuzB
public import CFSG.Sporadic.SuzOddCore.Perms
import Certificates.Kernel.SuzB17322.Facts

public section

namespace Certificates

open CertificateChecks

open Subgroup CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
  CFSG.HardMathSupport.Dickson.I271.TabSuzB in
theorem certificate17322 : permOfArr 1782 (xBArr (levels ())) ^ 3 = 1 ∧ permOfArr 1782 (xBArr (levels ())) ≠ 1 ∧
    Nat.card (closure (permsA 1782 (aGens ()))) = 729 ∧ permOfArr 1782 (xBArr (levels ())) ∈ suzM ∧
    closure (permsA 1782 (aGens ())) ≤
      centralizer {permOfArr 1782 (xBArr (levels ()))} ⊓ suzM ∧
    (∀ g ∈ centralizer {permOfArr 1782 (xBArr (levels ()))} ⊓ suzM,
      ∀ r ∈ closure (permsA 1782 (aGens ())), g * r * g⁻¹ ∈ closure (permsA 1782 (aGens ()))) ∧
    centralizer (closure (permsA 1782 (aGens ())) : Set (Equiv.Perm (Fin 1782))) ⊓
      (centralizer {permOfArr 1782 (xBArr (levels ()))} ⊓ suzM) ≤ closure (permsA 1782 (aGens ())) := KernelSuzB17322.main

end Certificates

module

public import CFSG.Walter.Ree.Bombieri.AppSpec
import Certificates.Kernel.Misc.Ree.K99

public section

namespace Certificates

open CFSG.Walter.Ree.Bombieri KernelRee

open CFSG.Walter.Ree.Bombieri in
theorem certificate7005 : ∀ k, 99 ≤ k → k ≤ 99 → k % 2 = 1 → AppOK k :=
  fun k h1 h2 _ => by
    obtain rfl : k = 99 := by omega
    exact K99.ok

end Certificates

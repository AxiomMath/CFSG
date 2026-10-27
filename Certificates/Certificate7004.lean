module

public import CFSG.Walter.Ree.Bombieri.AppSpec
import Certificates.Kernel.Misc.Ree.K93
import Certificates.Kernel.Misc.Ree.K95
import Certificates.Kernel.Misc.Ree.K97

public section

namespace Certificates

open CFSG.KC.Misc.Ree CFSG.Walter.Ree.Bombieri KernelRee

theorem appOK_chain_93 : ∀ i < 3, AppOK (93 + 2 * i) := by
  intro i hi
  interval_cases i
  exacts [K93.ok, K95.ok, K97.ok]

open CFSG.Walter.Ree.Bombieri in
theorem certificate7004 : ∀ k, 93 ≤ k → k ≤ 97 → k % 2 = 1 → AppOK k :=
  fun k h1 h2 h3 => odd_range (P := AppOK) (by norm_num) appOK_chain_93 k h1 (by omega) h3

end Certificates

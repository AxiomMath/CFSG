module

public import CFSG.Walter.Ree.Bombieri.AppSpec
import Certificates.Kernel.Misc.Ree.K81
import Certificates.Kernel.Misc.Ree.K83
import Certificates.Kernel.Misc.Ree.K85

public section

namespace Certificates

open CFSG.KC.Misc.Ree CFSG.Walter.Ree.Bombieri KernelRee

theorem appOK_chain_81 : ∀ i < 4, AppOK (81 + 2 * i) := by
  intro i hi
  interval_cases i
  exacts [K81.ok, K83.ok, K85.ok, K87.ok]

open CFSG.Walter.Ree.Bombieri in
theorem certificate7002 : ∀ k, 81 ≤ k → k ≤ 87 → k % 2 = 1 → AppOK k :=
  fun k h1 h2 h3 => odd_range (P := AppOK) (by norm_num) appOK_chain_81 k h1 (by omega) h3

end Certificates

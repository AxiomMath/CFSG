module

public import CFSG.Walter.Ree.Bombieri.AppSpec
import Certificates.Kernel.Misc.Ree.K89
import Certificates.Kernel.Misc.Ree.K91

public section

namespace Certificates

open CFSG.KC.Misc.Ree CFSG.Walter.Ree.Bombieri KernelRee

theorem appOK_chain_89 : ∀ i < 2, AppOK (89 + 2 * i) := by
  intro i hi
  interval_cases i
  exacts [K89.ok, K91.ok]

open CFSG.Walter.Ree.Bombieri in
theorem certificate7003 : ∀ k, 89 ≤ k → k ≤ 91 → k % 2 = 1 → AppOK k :=
  fun k h1 h2 h3 => odd_range (P := AppOK) (by norm_num) appOK_chain_89 k h1 (by omega) h3

end Certificates

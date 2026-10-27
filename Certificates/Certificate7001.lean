module

public import CFSG.Walter.Ree.Bombieri.AppSpec
import Certificates.Kernel.Misc.Ree.K71
import Certificates.Kernel.Misc.Ree.K73
import Certificates.Kernel.Misc.Ree.K77
import Certificates.Kernel.Misc.Ree.K79

public section

namespace Certificates

open CFSG.KC.Misc.Ree CFSG.Walter.Ree.Bombieri KernelRee

theorem appOK_chain_71 : ∀ i < 5, AppOK (71 + 2 * i) := by
  intro i hi
  interval_cases i
  exacts [K71.ok, K73.ok, K75.ok, K77.ok, K79.ok]

open CFSG.Walter.Ree.Bombieri in
theorem certificate7001 : ∀ k, 71 ≤ k → k ≤ 79 → k % 2 = 1 → AppOK k :=
  fun k h1 h2 h3 => odd_range (P := AppOK) (by norm_num) appOK_chain_71 k h1 (by omega) h3

end Certificates

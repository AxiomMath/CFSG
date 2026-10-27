module

public import CFSG.Walter.Ree.Bombieri.AppSpec
import Certificates.Kernel.Misc.Ree.K3
import Certificates.Kernel.Misc.Ree.K41
import Certificates.Kernel.Misc.Ree.K51
import Certificates.Kernel.Misc.Ree.K59
import Certificates.Kernel.Misc.Ree.K63
import Certificates.Kernel.Misc.Ree.K69

public section

namespace Certificates

open CFSG.KC.Misc.Ree CFSG.Walter.Ree.Bombieri KernelRee

theorem appOK_chain_3 : ∀ i < 34, AppOK (3 + 2 * i) := by
  intro i hi
  interval_cases i
  exacts [K3.ok, K5.ok, K7.ok, K9.ok, K11.ok, K13.ok, K15.ok, K17.ok, K19.ok, K21.ok, K23.ok,
    K25.ok, K27.ok, K29.ok, K31.ok, K33.ok, K35.ok, K37.ok, K39.ok, K41.ok, K43.ok, K45.ok, K47.ok,
    K49.ok, K51.ok, K53.ok, K55.ok, K57.ok, K59.ok, K61.ok, K63.ok, K65.ok, K67.ok, K69.ok]

open CFSG.Walter.Ree.Bombieri in
theorem certificate7000 : ∀ k, 3 ≤ k → k ≤ 69 → k % 2 = 1 → AppOK k :=
  fun k h1 h2 h3 => odd_range (P := AppOK) (by norm_num) appOK_chain_3 k h1 (by omega) h3

end Certificates

module

public import Certificates.Data.Antiflag
import CFSG.Certificates.Kernel.AntiflagSound
import Certificates.Kernel.Antiflag.Checks
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelAntiflag

open Certificates.Antiflag CFSG.KD.Antiflag CFSG.KC.Antiflag

theorem facts4 : Facts 4 :=
  facts_of_check 4 (W 0) (W 1) (fun s => W (2 + s)) (by decide) (by decide) (by decide)
    (by decide) ch7135_g4 ch7135_s4 fun s hs => by
      interval_cases s
      exacts [ch7135_t40, ch7135_t41, ch7135_t42, ch7135_t43]

theorem facts5 : Facts 5 :=
  facts_of_check 5 (W 6) (W 7) (fun s => W (8 + s)) (by decide) (by decide) (by decide)
    (by decide) ch7135_g5 ch7135_s5 fun s hs => by
      interval_cases s
      exacts [ch7135_t50, ch7135_t51, ch7135_t52, ch7135_t53]

end CertificateChecks.KernelAntiflag

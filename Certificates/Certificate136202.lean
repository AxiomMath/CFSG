module

public import CFSG.Certificates.Kernel.M3BFib.RootClaimSound
public import Certificates.Kernel.M3BFib.Lit
public import Certificates.Kernel.M3BFib.RootClaims
public import Certificates.Certificate16004

public section

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open CFSG.KC.M3BF CFSG.KD.M3BF
open Timmesfeld.M3B (B0 LA adOf sigW WT)

namespace CertificateChecks.Batch136202

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open CFSG.KC.M3BF CFSG.KD.M3BF
open Timmesfeld.M3B (B0 LA adOf sigW WT)

theorem tk_sound (k : ℕ) (j : ℕ) (t : PD) (hk : k = j + 1)
    (ht : adOfK LpM lk (sigW.getD j (WT.gen 0)) = t)
    (he : tDk k = adOf (B0 ()) (LA ()) (sigW.getD j (WT.gen 0))) :
    GoodPD t ∧ dK t = toD (tDk k) := by
  subst hk
  rw [he, ← ht, ← m3bf_lk]
  exact adOfK_sound _

theorem ts_sound : ∀ k < 4, GoodPD ([oneK, t1, t2, t3].getD k oneK) ∧
    dK ([oneK, t1, t2, t3].getD k oneK) = toD (tDk k) := by
  intro k hk
  interval_cases k
  · exact one_sound
  · exact tk_sound 1 0 t1 rfl m3bf_t1 rfl
  · exact tk_sound 2 1 t2 rfl m3bf_t2 rfl
  · exact tk_sound 3 2 t3 rfl m3bf_t3 rfl

theorem check_certificate : rootsOK () = true := rootsOK_of_F ts_sound m3br_roots

end CertificateChecks.Batch136202

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF in
theorem certificate136202 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.rootsOK () = true := CertificateChecks.Batch136202.check_certificate

end Certificates

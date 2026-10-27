module

public import Certificates.Data.U52Yamada
public import CFSG.Certificates.Kernel.EvenBN.YamadaKSound
import Certificates.Kernel.EvenBN.K27031
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.Batch27031

open CFSG.KC.Enum CFSG.KC.F4Mat CFSG.KC.YamadaK CFSG.Fischer
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo Certificates.U52Yamada

theorem c39_code (a : F4) : c39 (code a) = true := by
  obtain ⟨⟨c, hc⟩⟩ := a
  change c39 c = true
  interval_cases c
  exacts [k0, k1, k2, k3]

theorem check39_holds : Check39 := by
  intro a₁ b₁ a₂ a₃ a₄ b₄
  have h := all4_spec (all4_spec (all4_spec (all4_spec (all4_spec (c39_code a₁) b₁) a₂) a₃) a₄) b₄
  have := t39_sound (code_lt a₁) (code_lt b₁) (code_lt a₄) (code_lt b₄) h
  simp only [g4_code] at this
  exact this

theorem check39_true : check39 () = true := by
  unfold check39
  exact @decide_eq_true Check39
    (@decidable_of_iff _ Check39M check39M_iff (decCheck39M ())) check39_holds

end CertificateChecks.Batch27031

namespace Certificates

open CertificateChecks

theorem certificate27031 : Certificates.U52Yamada.check39 () = true := by
  exact CertificateChecks.Batch27031.check39_true

end Certificates

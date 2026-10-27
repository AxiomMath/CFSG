module

public import Certificates.Data.U52Yamada
public import CFSG.Certificates.Kernel.EvenBN.YamadaKSound
import Certificates.Kernel.EvenBN.K27030
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.Batch27030

open CFSG.KC.Enum CFSG.KC.F4Mat CFSG.KC.YamadaK CFSG.Fischer
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo Certificates.U52Yamada

theorem c3101_code (a : F4) : c3101 (code a) = true := by
  obtain ⟨⟨c, hc⟩⟩ := a
  change c3101 c = true
  interval_cases c
  exacts [k0, k1, k2, k3]

theorem check3101_holds : Check3101 := by
  intro a₁ b₁ a₂ a₃ a₄ b₄
  have h := all4_spec (all4_spec (all4_spec (all4_spec (all4_spec (c3101_code a₁) b₁) a₂) a₃)
    a₄) b₄
  have := t3101_sound (code_lt a₁) (code_lt b₁) (code_lt a₄) (code_lt b₄) h
  simp only [g4_code] at this
  exact this

theorem check3101_true : check3101 () = true := by
  unfold check3101
  exact @decide_eq_true Check3101
    (@decidable_of_iff _ Check3101M check3101M_iff (decCheck3101M ())) check3101_holds

end CertificateChecks.Batch27030

namespace Certificates

open CertificateChecks

theorem certificate27030 : Certificates.U52Yamada.check3101 () = true := by
  exact CertificateChecks.Batch27030.check3101_true

end Certificates

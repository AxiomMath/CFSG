module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.T22Glue
public import Certificates.Kernel.HMathieu.T12Glue
public import Certificates.Kernel.HMathieu.C260400
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.B45Mat CFSG.KC.HMathieu
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.B45Mat in
theorem certificate260400 :
    (
      forallGreedyAll pos24s2 inv24s2 (predQ 11 act24s2 true) 6 [] = true) ∧
    (
      forallGreedyAll pos24s2 inv24s2 (predQ 11 actC24s2 true) 6 [] = true) ∧
    (
      forallGreedyAll pos22s2 inv22s2 (predQ 10 act22s2 true) 5 [] = true) ∧
    (
      forallGreedyAll pos22s2 inv22s2 (predQ 10 actC22s2 false) 5 [] = true) ∧
    (
      forallGreedyAll pos12s2 inv12s2 (predQ 10 act12s2 true) 4 [] = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact forallGreedyAll_mats T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq act24s2
      T24.Mc (fun k hk => T24.act_el (by rwa [T24.len] at hk)) (fun a l => predQ 11 a true l)
      (fun a a' g l h => predQ_map 11 g true h) 6 (by rw [T24.len]; exact C260400.coc24)
  · exact forallGreedyAll_mats T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq actC24s2
      T24.Md (fun k hk => T24.actC_el (by rwa [T24.len] at hk)) (fun a l => predQ 11 a true l)
      (fun a a' g l h => predQ_map 11 g true h) 6 (by rw [T24.len]; exact C260400.code24)
  · exact forallGreedyAll_mats T22.gtabs (by rw [T22.len]; exact T22.lenOK.2) pos22s2_eq act22s2
      T22.Mc (fun k hk => T22.act_el (by rwa [T22.len] at hk)) (fun a l => predQ 10 a true l)
      (fun a a' g l h => predQ_map 10 g true h) 5 (by rw [T22.len]; exact C260400.coc22)
  · exact forallGreedyAll_mats T22.gtabs (by rw [T22.len]; exact T22.lenOK.2) pos22s2_eq actC22s2
      T22.Md (fun k hk => T22.actC_el (by rwa [T22.len] at hk)) (fun a l => predQ 10 a false l)
      (fun a a' g l h => predQ_map 10 g false h) 5 (by rw [T22.len]; exact C260400.code22)
  · exact forallGreedyAll_mats T12.gtabs (by rw [T12.len]; exact T12.lenOK.2) pos12s2_eq act12s2
      T12.Mc (fun k hk => T12.act_el (by rwa [T12.len] at hk)) (fun a l => predQ 10 a true l)
      (fun a a' g l h => predQ_map 10 g true h) 4 (by rw [T12.len]; exact C260400.w12)

end Certificates

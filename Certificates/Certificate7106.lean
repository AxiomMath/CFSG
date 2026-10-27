module

public import CFSG.Quasithin.H13.A5M22HatInputs
import Certificates.Certificate7068
import Certificates.Kernel.HMathieu.Wit7106K
import Certificates.Kernel.HMathieu.T22Elems
import CFSG.Certificates.Kernel.HMathieu.Wit22KSound
import CFSG.Certificates.Kernel.MathieuAut.ColsKUse

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat CFSG.KS.MathieuAut CFSG.KC.HMathieu
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat in
theorem certificate7106 :
    (∀ a ∈ pool22, inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1)
    ∧ (∀ p < T22s2.n, p ≠ T22s2.one → T22s2.mulIdx p p = T22s2.one → wit22OK p = true) := by
  refine ⟨fun a ha => ?_, fun p hp h1 h2 => ?_⟩
  · obtain ⟨-, h1, h2⟩ := memK_spec (P := fun a => a[0]! == 0 && a[1]! == 1) k7106_memK a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2⟩
  · obtain ⟨⟨hc, hn, -⟩, -⟩ := (Certificates.certificate7068)
    obtain ⟨-, -, hone, -, hmul, -⟩ := PT.check_spec hc
    have hsq : inv24 (T22s2.elems[p]!) = true := by
      simp only [inv24, List.all_eq_true, List.mem_range, beq_iff_eq]
      intro i hi
      rw [← hmul p hp p hp i hi, h2]
      exact hone i hi
    have hp0 : p ≠ 0 := h1
    have hpE : p < T22.E.length := by
      rw [T22.n_size, T22.elems_eq] at hp
      simpa using hp
    have hP : ∀ i < 6, vpK (poolP.getD i 0) = true ∧ vpK (poolI.getD i 0) = true ∧
        unpk (poolP.getD i 0) = pool22[i]! ∧ unpk (poolI.getD i 0) = invArr pool22[i]! := by
      intro i hi
      have := List.all_eq_true.1 k7106_pool i (List.mem_range.2 hi)
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
    have hwit := k7106_witK
    rw [← chk7106K_eq hP (List.all_eq_true.1 T22.vpE)] at hwit
    have hk := List.all_eq_true.1 hwit p (List.mem_range.2 hpE)
    rw [← T22.elems_eq] at hk
    simp only [hsq, hp0, Bool.or_eq_true, beq_iff_eq, Bool.not_true, Bool.false_eq_true,
      or_false, false_or] at hk
    exact hk

end Certificates

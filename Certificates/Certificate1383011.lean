module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.QuandleCheck
import Certificates.Kernel.MinusAut.Checks
import Certificates.Kernel.MinusQuandle.Checks
import CFSG.Certificates.Kernel.MinusAutSound

public section

namespace CertificateChecks.KernelMinusAut

open CFSG.KD.MinusAut CFSG.KC.MinusAut CertificateChecks.KernelMinusQ

private theorem main_all {c : ℕ} (hc : c < 65) : mainA R PP XX YY QQ (kmask homs) c = true := by
  by_cases h0 : c < 9
  · exact mainOK_spec ch1383011m_0 (Nat.zero_le _) (by omega)
  by_cases h1 : c < 17
  · exact mainOK_spec ch1383011m_1 (by omega) (by omega)
  by_cases h2 : c < 25
  · exact mainOK_spec ch1383011m_2 (by omega) (by omega)
  by_cases h3 : c < 33
  · exact mainOK_spec ch1383011m_3 (by omega) (by omega)
  by_cases h4 : c < 41
  · exact mainOK_spec ch1383011m_4 (by omega) (by omega)
  by_cases h5 : c < 49
  · exact mainOK_spec ch1383011m_5 (by omega) (by omega)
  by_cases h6 : c < 57
  · exact mainOK_spec ch1383011m_6 (by omega) (by omega)
  exact mainOK_spec ch1383011m_7 (by omega) (by omega)

end CertificateChecks.KernelMinusAut

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMinusAut in
open CFSG.OddTranspositions.PartThree in
theorem certificate1383011 : (∀ i : Fin 65, ∃ w : List (Fin 65), w.foldr minusQuandleTf 0 = i) ∧
    ∀ σ : Fin 65 → Fin 65, Function.Injective σ →
      (∀ i j : Fin 65, σ (minusQuandleTf i j) = minusQuandleTf (σ i) (σ j)) → σ 0 = 0 →
        ∃ w : List (Fin 65), ∀ k : Fin 65, σ k = w.foldr minusQuandleTf k :=
  ⟨CFSG.KC.MinusAut.trans_word KernelMinusQ.rows_ok trans_ok,
    CFSG.KC.MinusAut.hom_word KernelMinusQ.rows_ok ord_ok homs_ok (fun _ hc => main_all hc)⟩

end Certificates

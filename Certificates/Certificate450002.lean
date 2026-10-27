module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshQCheck
import Certificates.Kernel.YoshQ.GlueL45
import Certificates.Kernel.YoshQ.GlueModel
import Certificates.Kernel.YoshQ.GlueFacts
import Certificates.Kernel.YoshQ.GlueBound

public section

open CFSG.CosetTable CFSG.EvenSporadicStandard.M12Std.Yosh
open CertificateChecks.KernelYoshQ CFSG.EvenSporadicStandard.M12Std.Yosh

namespace Certificates

open CertificateChecks

theorem certificate450002 : yoshQCheck = true := by
  simp only [yoshQCheck, lemma4Check_true, lemma5Check_true, lemma5ModelCheck_true,
    modelFactsCheck_true, Bool.and_self]

theorem certificate450002.rel4_card : ∀ α β, α < 2 → β < 2 →
    Finite (PG 8 (rel4 α β)) ∧ Nat.card (PG 8 (rel4 α β)) ≤ 1536 :=
  KernelYoshQ.rel4_card

theorem certificate450002.relE_card : Finite (PG 6 relE) ∧ Nat.card (PG 6 relE) ≤ 128 :=
  KernelYoshQ.relE_card

theorem certificate450002.relN_card : ∀ α k, α < 2 → k < 2 →
    Finite (PG 9 (relN α α k)) ∧ Nat.card (PG 9 (relN α α k)) ≤ 3072 :=
  KernelYoshQ.relN_card

end Certificates

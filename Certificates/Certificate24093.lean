module

public import CFSG.Sporadic.Recognition.M22MultiplierInputs
import Certificates.Kernel.MatCC.M22.Tabs
import Certificates.Kernel.MatCC.M22.TabCheck
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.Sporadic.Recognition.M22Multiplier CFSG.KC.MiscCoset

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.Sporadic.Recognition.M22Multiplier in
theorem certificate24093 : (m22TabCheck = true) ∧
    (Finite (PG 2 m22Rels) ∧ Nat.card (PG 2 m22Rels) ≤ 443520) := by
  obtain ⟨f, c⟩ := TableFact.card_restrict m22Rels (by norm_num) (subsetOf 2 [1]) (by decide)
    CFSG.KBFact.F24093w CFSG.KBFact.F24093v
  exact ⟨KernelM22Tab.m22TabCheck_true, f, c.trans (by norm_num)⟩

end Certificates

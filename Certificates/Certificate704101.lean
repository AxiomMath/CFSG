module

public import Certificates.Data.ThirteenListThreeCoverInputs
import Certificates.Kernel.CoverU43.Glue
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.OddTranspositions.PartFour.CoverCard

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.OddTranspositions.PartFour.CoverCard in
theorem certificate704101 : Finite (PG 6 coverWords) ∧ Nat.card (PG 6 coverWords) ≤ 19595520 := by
  obtain ⟨f, c⟩ := TableFact.card_restrict coverWords (by norm_num) (subsetOf 6 [0, 1, 2, 3, 4])
    (by decide) KernelCoverU43.factH KernelCoverU43.factT
  exact ⟨f, c.trans (by norm_num)⟩

end Certificates

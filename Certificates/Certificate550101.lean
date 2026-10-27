module

public import Certificates.Data.WPres
import Certificates.Kernel.CosPres.F550101
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.CosetTablePresented

public section

open CFSG.CosetTable CFSG.ClassicalInvolution.Sp62Rec.I1 CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.ClassicalInvolution.Sp62Rec.I1 in
theorem certificate550101 : Finite (PG 10 (relsW ())) ∧ Nat.card (PG 10 (relsW ())) ≤ 23040 := by
  obtain ⟨f, c⟩ := TableFact.card_restrict (relsW ()) (by norm_num) (subsetOf 10 [0, 1, 2, 3, 4])
    (by decide) CFSG.KBFact.F550101b CFSG.KBFact.F550101a
  exact ⟨f, c.trans (by norm_num)⟩

end Certificates

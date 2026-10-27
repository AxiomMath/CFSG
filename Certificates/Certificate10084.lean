module

public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.CFSGNative.Co2Smith.Sp6Pres
import Certificates.Kernel.Co2Smith.Sp6KB
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.Sporadic.Co2Smith.Native CFSG.CosetTable

namespace Certificates

open CFSG.CosetTable in
theorem certificate10084 :
    (Finite (PG 8 CFSG.Sporadic.Co2Smith.Native.sp6Rels) ∧
      Nat.card (PG 8 CFSG.Sporadic.Co2Smith.Native.sp6Rels) ≤ 1451520)
    ∧ (Finite (PG 8 CFSG.Sporadic.Co2Smith.Native.sp6CoverR) ∧
      Nat.card (PG 8 CFSG.Sporadic.Co2Smith.Native.sp6CoverR) ≤ 2903040) :=
  ⟨CFSG.KC.MiscCoset.TableFact.card_restrict (sp6Rels ()) (by norm_num) [6, 7] (by norm_num)
      CFSG.KBFact.K10084a CFSG.KBFact.K10084b,
    CFSG.KC.MiscCoset.TableFact.card_restrict (sp6CoverR ()) (by norm_num) [6, 7] (by norm_num)
      CFSG.KBFact.K10084c CFSG.KBFact.K10084d⟩

end Certificates

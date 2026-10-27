module

public import Certificates.Data.CFSGNative.CTIB.Coset
import CFSG.Certificates.Kernel.BabyMonster.CTIBRecsSound
import CFSG.Certificates.Kernel.Common.StrLits
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic

public section

open CFSG.Monster.B.CTIB.Native

namespace CertificateChecks.Batch3111

open CFSG.Monster.B.CTIB.Native

theorem orbitRecs_len6 : (orbitRecs 6).length = 529 := by
  change (orbitRecs.pairs (parseNats orbitStr6)).length = 529
  str_lits orbitStr6
  exact pairs_len_of (by quickRfl)

theorem orbitRecs_len8 : (orbitRecs 8).length = 37 := by
  change (orbitRecs.pairs (parseNats orbitStr8)).length = 37
  str_lits orbitStr8
  exact pairs_len_of (by quickRfl)

theorem orbitRecs_len10 : (orbitRecs 10).length = 3 := by
  change (orbitRecs.pairs (parseNats orbitStr10)).length = 3
  str_lits orbitStr10
  exact pairs_len_of (by quickRfl)

theorem orbitRecs_len8_neg : (!((orbitRecs 8).length == 36)) = true := by
  change (!((orbitRecs.pairs (parseNats orbitStr8)).length == 36)) = true
  str_lits orbitStr8
  rw [pairs_parse]
  · quickRfl
  · quickRfl

end CertificateChecks.Batch3111

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB.Native in
theorem certificate3111 : (orbitRecs 6).length = 529 ∧ (orbitRecs 8).length = 37 ∧ (orbitRecs 10).length = 3 :=
  ⟨CertificateChecks.Batch3111.orbitRecs_len6, CertificateChecks.Batch3111.orbitRecs_len8, CertificateChecks.Batch3111.orbitRecs_len10⟩

end Certificates

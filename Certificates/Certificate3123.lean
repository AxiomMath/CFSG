module

public import Certificates.Data.CFSGNative.CTIB.Coset
import CFSG.Certificates.Kernel.BabyMonster.CTIBRecsSound
import CFSG.Certificates.Kernel.Common.StrLits
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic
import all Init.Data.Nat.ToString
import Std.Tactic.BVDecide.Normalize.Prop

public section

open CFSG.Monster.B.CTIB.Native

namespace CertificateChecks.Batch3123

open CFSG.Monster.B.CTIB.Native

theorem orbitRecs_mem6 : ∀ q ∈ [(43, 128), (61, 128), (10541, 64), (26925, 128), (46090, 64)],
    q ∈ orbitRecs 6 := by
  change ∀ q ∈ _, q ∈ orbitRecs.pairs (parseNats orbitStr6)
  str_lits orbitStr6
  exact pairs_mem_of (by quickRfl)

theorem orbitRecs_mem8 : ∀ q ∈ [(0, 256), (128, 512), (35764, 256)], q ∈ orbitRecs 8 := by
  change ∀ q ∈ _, q ∈ orbitRecs.pairs (parseNats orbitStr8)
  str_lits orbitStr8
  exact pairs_mem_of (by quickRfl)

theorem orbitRecs_mem10 : ∀ q ∈ [(107, 2048), (66038, 2048)], q ∈ orbitRecs 10 := by
  change ∀ q ∈ _, q ∈ orbitRecs.pairs (parseNats orbitStr10)
  str_lits orbitStr10
  exact pairs_mem_of (by quickRfl)

theorem orbitRecs_mem6_neg : (!((orbitRecs 6).any fun r => r.1 == 43 && r.2 == 64)) = true := by
  change (!((orbitRecs.pairs (parseNats orbitStr6)).any fun r => r.1 == 43 && r.2 == 64)) = true
  str_lits orbitStr6
  rw [pairs_parse]
  · quickRfl
  · quickRfl

end CertificateChecks.Batch3123

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB.Native in
theorem certificate3123 : (43, 128) ∈ orbitRecs 6 ∧ (61, 128) ∈ orbitRecs 6 ∧ (10541, 64) ∈ orbitRecs 6 ∧
      (26925, 128) ∈ orbitRecs 6 ∧ (46090, 64) ∈ orbitRecs 6 ∧ (0, 256) ∈ orbitRecs 8 ∧
      (128, 512) ∈ orbitRecs 8 ∧ (35764, 256) ∈ orbitRecs 8 ∧ (107, 2048) ∈ orbitRecs 10 ∧
      (66038, 2048) ∈ orbitRecs 10 := by
  have h6 := CertificateChecks.Batch3123.orbitRecs_mem6
  have h8 := CertificateChecks.Batch3123.orbitRecs_mem8
  have h10 := CertificateChecks.Batch3123.orbitRecs_mem10
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h6 h8 h10
  exact ⟨h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2, h8.1, h8.2.1, h8.2.2, h10.1, h10.2⟩

end Certificates

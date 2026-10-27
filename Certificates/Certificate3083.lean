module

public import CFSG.Monster.B.TwoA.Unitary.TwentyData
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

open CFSG.Monster.B.TwoA.Unitary CFSG.KC.U6Orb

namespace CertificateChecks.Batch3083

open CFSG.Monster.B.TwoA.Unitary CFSG.KC.U6Orb

theorem kWords : allL (boundL 17) u20Words.toList = true := by quickRfl

end CertificateChecks.Batch3083

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Unitary in
theorem certificate3083 : ∀ j < 400, ∀ k ∈ u20Words[j]!, k < 17 := by
  intro j _ k hk
  by_cases hj : j < u20Words.size
  · rw [getElem!_toList u20Words hj] at hk
    exact (boundL_iff _ _).1 ((allL_iff _ _).1 CertificateChecks.Batch3083.kWords _ (List.getElem_mem _)) k hk
  · rw [getElem!_neg u20Words j hj] at hk
    exact absurd hk List.not_mem_nil

end Certificates

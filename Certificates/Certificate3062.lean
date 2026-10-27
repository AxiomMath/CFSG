module

public import CFSG.Monster.B.TwoA.Unitary.BData
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

open CFSG.Monster.B.TwoA.Unitary CFSG.KC.U6Orb

namespace CertificateChecks.Batch3062

open CFSG.Monster.B.TwoA.Unitary CFSG.KC.U6Orb

theorem kDist : nodupM (mapL (fun x => Nat.mod x 891) b6IsoArr.toList) 0 = true := by quickRfl

theorem kLen : Nat.beq (lenL b6IsoArr.toList) 891 = true := by quickRfl

end CertificateChecks.Batch3062

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Unitary in
theorem certificate3062 : ∀ i < 891, ∀ j < 891, b6IsoArr[i]! % 891 = b6IsoArr[j]! % 891 → i = j := by
  intro i hi j hj e
  have hs : b6IsoArr.size = 891 := by
    have := CertificateChecks.Batch3062.kLen
    rwa [Nat.beq_eq, lenL_eq, Array.length_toList] at this
  have hnd := (nodupM_spec _ _ CertificateChecks.Batch3062.kDist).1
  rw [mapL_eq] at hnd
  rw [getElem!_toList b6IsoArr (hs ▸ hi), getElem!_toList b6IsoArr (hs ▸ hj)] at e
  have hi' : i < (b6IsoArr.toList.map fun x => Nat.mod x 891).length := by simp [hs, hi]
  have hj' : j < (b6IsoArr.toList.map fun x => Nat.mod x 891).length := by simp [hs, hj]
  have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := hi') (hj := hj')).1
    (by simp only [List.getElem_map]; exact e)
  exact this

end Certificates

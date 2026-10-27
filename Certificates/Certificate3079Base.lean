
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
public import Certificates.Kernel.MonsterB.Co2Vecs
public import Certificates.Kernel.MonsterB.Tau1408Data
public import CFSG.Monster.B.TwoA.Unitary.NData
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census
open CFSG.KC.U6Orb CFSG.KLie.CT CertificateChecks.KernelMonB CertificateChecks.Tau1408

namespace CertificateChecks.Batch3079

set_option maxRecDepth 100000

theorem kVec : boundL (pw2 22) n6VecArr.toList = true := by quickRfl

theorem kTau : boundL (pw2 22) o14VecArr.toList = true := by quickRfl

theorem kRow : shapeL 22 (pw2 22) n6RowArr.toList = true := by quickRfl

theorem kShift : memOK n6VecArr.toList 6144 (Co2V.F 0) 24 IA 12 2300 891 6144 = true := by
  quickRfl

theorem kMem : memOK o14VecArr.toList 0 (Co2V.F 0) 24 IB 12 2300 1408 6144 = true := by
  quickRfl

theorem kSort : sortOK (mapL (fun x => Nat.xor 6144 x) n6VecArr.toList ++ o14VecArr.toList) SC 12
    2299 = true := by
  quickRfl

theorem kEdge : edgeLOK o14VecArr.toList n6RowArr.toList ET (tabE 17 11) 1408 17 = true := by
  quickRfl

theorem kReplay : replayDOK ET (tabE 17 11) 17 1408 = true := by quickRfl

theorem kSizes : n6VecArr.size = 891 ∧ o14VecArr.size = 1408 ∧ n6RowArr.size = 17 ∧
    o14VecArr[0]! = 60 := by
  decide +kernel

theorem pg_eq (X t : ℕ) : CFSG.KC.Enum.pg 24 (CFSG.KS.mask 24) X t = fget X t 24 := by
  change (X >>> (24 * t)) &&& CFSG.KS.mask 24 = (X >>> (t * 24)) &&& maskN 24
  rw [Nat.mul_comm]
  rfl

theorem contains_of {y : ℕ} (h : ∃ t < 2300, fget (Co2V.F 0) t 24 = y) :
    (Native.vectors ()).contains y = true := by
  obtain ⟨t, ht, rfl⟩ := h
  rw [← pg_eq]
  exact vectors_contains ht

theorem shift_codes : ∀ j < 891, Native.vectors.contains (6144 ^^^ n6VecArr[j]!) = true ∧
    6144 ^^^ n6VecArr[j]! < 2 ^ 22 ∧ 6144 ^^^ n6VecArr[j]! ≠ 6144 := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := memOK_sound kSizes.1 kVec kShift j hj
  exact ⟨contains_of h1, h2, h3⟩

theorem tau_codes : ∀ i < 1408, Native.vectors.contains o14VecArr[i]! = true ∧
    o14VecArr[i]! ≠ 6144 := by
  intro i hi
  obtain ⟨h1, -, h3⟩ := memOK_sound kSizes.2.1 kTau kMem i hi
  rw [Nat.zero_xor] at h1 h3
  exact ⟨contains_of h1, h3⟩

theorem kNodup : (mapL (fun x => Nat.xor 6144 x) n6VecArr.toList ++ o14VecArr.toList).Nodup :=
  (sortOK_sound kSort).1

theorem kDist : o14VecArr.toList.Nodup := (List.nodup_append.1 kNodup).2.1

theorem disjoint : ∀ i < 1408, ∀ j < 891, o14VecArr[i]! ≠ 6144 ^^^ n6VecArr[j]! := by
  intro i hi j hj e
  have hB : o14VecArr[i]! ∈ o14VecArr.toList := by
    rw [getElem!_toList _ (by rw [kSizes.2.1]; exact hi)]
    exact List.getElem_mem _
  have hA : o14VecArr[i]! ∈ mapL (fun x => Nat.xor 6144 x) n6VecArr.toList := by
    rw [mapL_eq, List.mem_map, e]
    refine ⟨n6VecArr[j]!, ?_, rfl⟩
    rw [getElem!_toList _ (by rw [kSizes.1]; exact hj)]
    exact List.getElem_mem _
  exact (List.nodup_append.1 kNodup).2.2 _ hA _ hB rfl

theorem orbit : natCertOK genAct 17 (fun a => decide (a < 2 ^ 22)) 60 tauCert = true ∧
    tauCert.pts = o14VecArr :=
  bfs_sound (act := genAct) (fuel := 1500) (fun _ _ => rfl) kSizes.2.1 (by norm_num)
    kSizes.2.2.1 kSizes.2.2.2 (by norm_num) kTau kDist kRow kEdge kReplay

end CertificateChecks.Batch3079

namespace Certificates

end Certificates

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Certificates.Data.CFSGNative.CTIB.Coset
import Certificates.Certificate3110
import Certificates.Kernel.BabyMonster.CTIB.Outer3122
import Certificates.Kernel.BabyMonster.CTIB.CosetQBind
import Certificates.Kernel.BabyMonster.CTIB.QK
import CFSG.Certificates.Kernel.BabyMonster.OrbTreeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.CTIB.Native CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbT CFSG.KC.Bfs
  CertificateChecks.KernelBM.CTIB CertificateChecks.KernelBM.CTIB.CosetQ

namespace CertificateChecks.Batch3122

open CFSG.Monster.B.CTIB.Native CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbT CFSG.KC.Bfs
  CertificateChecks.KernelBM.CTIB CertificateChecks.KernelBM.CTIB.CosetQ

private theorem qmul_4204845 : qmul gArr 10541 (2 ^ 22) = 4204845 := by
  rw [← QK.mulQ_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

private theorem isInv_4204845 :
    isInv gArr (liftImgsN 6).toArray (sqCode 6) 4204845 = true := by
  rw [isInv, lift6, ← QK.autQ_eq, ← QK.mulQ_eq, ← QK.mulQ_eq]
  quickRfl

private theorem rankOff6 (j : ℕ) : rankOff 6 + j = j := by simp [rankOff]

private theorem gA6_eq {j : ℕ} (hj : j < 15) :
    wordAut (genInvImgs ()) (centWordN 6 j) = arrOf (nthN Gs j) := by
  have h := words_of Certificates.certificate3110.1 (k := 6) (j := j) (by rw [rankOff6]; omega)
  rw [rankOff6] at h
  rw [h, word_imgs symFacts ct_eq _ (steps_of (by omega)), (wOK_eq (by omega)).1]

private theorem fuse_act {k : ℕ} (hk : k < 37) (x : ℕ) :
    fuseAct (liftImgsN 6).toArray
      ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)).toArray
      ((List.range 15).map fun j => deltaN 6 j).toArray k x = Outer3122.act k x := by
  by_cases h : k < 22
  · have hb : Nat.blt k 22 = true := blt_iff.2 h
    have e : Outer3122.act k x = mulQ LOq (fld32 AH6 k) (mulQ LOq x (2 ^ k)) := by
      unfold Outer3122.act fuseK
      rw [hb]
      rfl
    rw [e, fuseAct, if_pos h, qconj, lift6, arrOf_getD AH6 h, QK.mulQ_eq, QK.mulQ_eq]
  · obtain ⟨t, rfl⟩ : ∃ t, k = 22 + t := ⟨k - 22, by omega⟩
    have ht : t < 15 := by omega
    have hb : Nat.blt (22 + t) 22 = false := Bool.eq_false_iff.2 fun e => h (blt_iff.1 e)
    have e : Outer3122.act (22 + t) x = mulQ LOq (nthN Ds t) (autQ LOq (nthN Gs t) x) := by
      unfold Outer3122.act fuseK
      rw [hb]
      change mulQ LOq (nthN Ds (22 + t - 22)) (autQ LOq (nthN Gs (22 + t - 22)) x) = _
      rw [Nat.add_sub_cancel_left]
    rw [e, fuseAct, if_neg h, Nat.add_sub_cancel_left, getD_range_map _ _ ht,
      getD_range_map _ _ ht, gA6_eq ht, fuse, QK.autQ_eq, QK.mulQ_eq, deltaN, rankOff6,
      ds_eq t (by omega)]

private theorem fuseBfs_4204845 :
    (natBfs (fuseAct (liftImgsN 6).toArray
      ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)).toArray
      ((List.range 15).map fun j => deltaN 6 j).toArray) 37 46090 65).1.contains 4204845 =
      true := by
  obtain ⟨hS, hcard, -⟩ := orbT_reach (fun k hk x => fuse_act hk x) Outer3122.inc Outer3122.clos
    Outer3122.tree (by decide) (beq_iff.1 Outer3122.root)
  rw [native_natBfs_eq]
  obtain ⟨hmem, -, -⟩ := gBfs_listing (key := id) (fuel := 65) _ hS (fun _ _ _ _ e => e)
    ((Nat.le_of_eq hcard).trans (by decide))
  have hx : (4204845 : ℕ) ∈ ptsF 64 CFSG.KD.Outer3122.S :=
    mem_ptsF.2 ⟨32, by decide, beq_iff.1 Outer3122.target⟩
  have hy := (hmem 4204845).2 hx
  exact Array.contains_iff_mem.2 hy

end CertificateChecks.Batch3122

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB.Native in
theorem certificate3122 : (qmul CFSG.Monster.B.CTIB.Native.gArr 10541 (2 ^ 22) = 4204845)
    ∧ (CFSG.Monster.B.CTIB.Native.isInv CFSG.Monster.B.CTIB.Native.gArr (liftImgsN 6).toArray (sqCode 6) 4204845 = true)
    ∧ ((CFSG.Monster.B.CTIB.Native.natBfs (fuseAct (liftImgsN 6).toArray
       ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)).toArray
       ((List.range 15).map fun j => deltaN 6 j).toArray) 37 46090 65).1.contains 4204845 = true) :=
  ⟨CertificateChecks.Batch3122.qmul_4204845, CertificateChecks.Batch3122.isInv_4204845, CertificateChecks.Batch3122.fuseBfs_4204845⟩

end Certificates

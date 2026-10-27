module

public import CFSG.Monster.B.CTIB.Rank2158WitnessInputs
import Certificates.Certificate3110
import Certificates.Kernel.BabyMonster.CTIB.CosetQBind
import Certificates.Kernel.BabyMonster.CTIB.QK
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.CTIB.Native CFSG.Monster.B.CTIB CFSG.KC.BM CFSG.KC.BM.CosetQ
  CertificateChecks.KernelBM.CTIB CertificateChecks.KernelBM.CTIB.CosetQ

namespace CertificateChecks.Batch3121

open CFSG.Monster.B.CTIB.Native CFSG.Monster.B.CTIB CFSG.KC.BM CFSG.KC.BM.CosetQ
  CertificateChecks.KernelBM.CTIB CertificateChecks.KernelBM.CTIB.CosetQ

private theorem w2158_eq : w2158 = [0, 1, 0, 0, 0, 0, 1, 0, 2, 0].flatMap symLetters := by
  decide +kernel

private theorem autApply_w2158 : autApply gArr (wordAut (genInvImgs ()) w2158) 1 = 4456968 := by
  rw [w2158_eq, word_imgs symFacts ct_eq _ (by decide), ← QK.autQ_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

private theorem qmul_2158 : qmul gArr 10541 4456968 = 273189 := by
  rw [← QK.mulQ_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

private theorem qmul_2158N :
    qmul gArr (autApply gArr (liftImgsN 6).toArray 4456968) 10541 = 273189 := by
  rw [lift6, ← QK.autQ_eq, ← QK.mulQ_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

private theorem isInv_273189 : isInv gArr (liftImgsN 6).toArray (sqCode 6) 273189 = true := by
  rw [isInv, lift6, ← QK.autQ_eq, ← QK.mulQ_eq, ← QK.mulQ_eq]
  quickRfl

private theorem rankOff6 (j : ℕ) : rankOff 6 + j = j := by simp [rankOff]

private theorem gA6_eq {j : ℕ} (hj : j < 15) :
    wordAut (genInvImgs ()) (centWordN 6 j) = arrOf (nthN Gs (0 + j)) := by
  have h := words_of Certificates.certificate3110.1 (k := 6) (j := j) (by rw [rankOff6]; omega)
  rw [rankOff6] at h
  rw [h, word_imgs symFacts ct_eq _ (steps_of (by omega)), (wOK_eq (by omega)).1, Nat.zero_add]

private theorem act_eq : fuseAct (liftImgsN 6).toArray
    ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)).toArray
    ((List.range 15).map fun j => deltaN 6 j).toArray =
    fuseAct (arrOf AH6) ((List.range 15).map fun j => arrOf (nthN Gs (0 + j))).toArray
      ((List.range 15).map fun j => nthN Ds (0 + j)).toArray := by
  have hgL : ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)) =
      (List.range 15).map fun j => arrOf (nthN Gs (0 + j)) :=
    List.map_congr_left fun j hj => gA6_eq (List.mem_range.1 hj)
  have hdL : ((List.range 15).map fun j => deltaN 6 j) =
      (List.range 15).map fun j => nthN Ds (0 + j) :=
    List.map_congr_left fun j hj => by
      rw [deltaN, rankOff6, ds_eq _ (by have := List.mem_range.1 hj; omega), Nat.zero_add]
  rw [lift6, hgL, hdL]

private theorem rec61 : repOf PT6 (fld32 RT6 1) = 61 ∧
    ((Finset.range 529).filter (fun q => labOf PT6 q = labOf PT6 (fld32 RT6 1))).sum
      (sizeOf 6 PT6) = 32768 := by
  have h := congrArg (fun l : List (ℕ × ℕ × ℕ) => (l.getD 1 (0, 0, 0)).2.1) fr6
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by decide : 1 < 5),
    Option.map_some, Option.getD_some] at h
  rw [(root6 1 (by decide)).2.2, ← h]
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem pt273189 : ptIdxK LOq AH6 6 Bs6 T6 VT6 PT6 273189 ≠ 1024 ∧
    labOf PT6 (ptIdxK LOq AH6 6 Bs6 T6 VT6 PT6 273189) = 1 := by
  have h : (ptIdxK LOq AH6 6 Bs6 T6 VT6 PT6 273189 != 1024) = true := by quickRfl
  exact ⟨bne_iff_ne.1 h, Nat.eq_of_beq_eq_true (by quickRfl)⟩

private theorem fuseBfs_273189 :
    (natBfs (fuseAct (liftImgsN 6).toArray
      ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)).toArray
      ((List.range 15).map fun j => deltaN 6 j).toArray) 37 61 32769).1.contains 273189 =
      true := by
  set act := fuseAct (arrOf AH6) ((List.range 15).map fun j => arrOf (nthN Gs (0 + j))).toArray
    ((List.range 15).map fun j => nthN Ds (0 + j)).toArray with hact
  have hact1 : ∀ i < 22, ∀ n, act i n = qconj (gArr ()) (arrOf AH6) i n := fun i hi n => by
    rw [hact, fuseAct, ite_eq_left hi]
  have hact2 : ∀ t < 15, ∀ n,
      act (22 + t) n = fuse (gArr ()) (arrOf (nthN Gs (0 + t))) (nthN Ds (0 + t)) n :=
    fun t ht n => by
      rw [hact, fuseAct, ite_eq_right (by omega), (by omega : 22 + t - 22 = t),
        getD_range_map _ _ ht, getD_range_map _ _ ht]
  obtain ⟨hp, h0, hlab1⟩ := root6 1 (by decide)
  obtain ⟨S, hSm, hScard, -, hSrep⟩ :=
    forb_facts rank6 act hact1 hact2 hp ((trOK_spec (rank6.tr _ hp)).1 h0)
  obtain ⟨h61, hsz⟩ := rec61
  rw [h61] at hSm
  rw [hsz] at hScard
  have hS := setup_of rank6.symm rank6.setup
  obtain ⟨hne, hl⟩ := pt273189
  let u : CosetQ.QC (gArr ()) := ⟨273189, by decide⟩
  have hne' : ptIdxK (loOf (gArr ())) AH6 6 Bs6 T6 VT6 PT6 u.1 ≠ 1024 := by
    rw [← loq_eq]
    exact hne
  obtain ⟨hq, e, he⟩ := pt_target rank6 hne'
  rw [← loq_eq] at hq he
  have hrep : repOf PT6 (ptIdxK LOq AH6 6 Bs6 T6 VT6 PT6 273189) ∈ S :=
    (hSrep _ hq).2 (hl.trans hlab1.symm)
  have hr1 : Reach (qconj (gArr ()) (arrOf AH6)) 22
      (repQ (G := gArr ()) PT6 (ptIdxK LOq AH6 6 Bs6 T6 VT6 PT6 273189)).1 273189 :=
    (reach_qconj hS _ 273189).2 ⟨e, congrArg Subtype.val he⟩
  have hsub : ∀ i < 22, ∃ i' < 37, ∀ n, qconj (gArr ()) (arrOf AH6) i n = act i' n :=
    fun i hi => ⟨i, by omega, fun n => (hact1 i hi n).symm⟩
  have hx : (273189 : ℕ) ∈ S := (hSm _).2 (reach_trans hsub ((hSm _).1 hrep) hr1)
  rw [act_eq]
  obtain ⟨-, hmem, -⟩ := natBfs_native (valid := fun _ => true) (fuel := 32769) S
    (fun x => (hSm x).symm) (fun _ _ => rfl) (by rw [hScard]; decide)
  exact Array.contains_iff_mem.2 ((hmem 273189).2 hx)

end CertificateChecks.Batch3121

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB.Native CFSG.Monster.B.CTIB in
theorem certificate3121 : (autApply gArr (wordAut (genInvImgs ()) w2158) 1 = 4456968)
    ∧ (qmul gArr 10541 4456968 = 273189)
    ∧ (qmul gArr (autApply gArr (liftImgsN 6).toArray 4456968) 10541 = 273189)
    ∧ (isInv gArr (liftImgsN 6).toArray (sqCode 6) 273189 = true)
    ∧ ((natBfs (fuseAct (liftImgsN 6).toArray
       ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)).toArray
       ((List.range 15).map fun j => deltaN 6 j).toArray) 37 61 32769).1.contains 273189 = true) :=
  ⟨CertificateChecks.Batch3121.autApply_w2158, CertificateChecks.Batch3121.qmul_2158, CertificateChecks.Batch3121.qmul_2158N, CertificateChecks.Batch3121.isInv_273189,
    CertificateChecks.Batch3121.fuseBfs_273189⟩

end Certificates

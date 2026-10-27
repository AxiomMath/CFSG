module

public import CFSG.Monster.B.GSide.HInnerFusionY3CertInputs
import Certificates.Kernel.BabyMonster.CTIB.Y3136
import Certificates.Kernel.BabyMonster.CTIB.CosetQBind
import Certificates.Kernel.BabyMonster.CTIB.QK
import Certificates.Kernel.BabyMonster.CTIB.InnerTab
import Certificates.Kernel.BabyMonster.Census
import CFSG.Certificates.Kernel.BabyMonster.OrbTreeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.B.GSide CFSG.KC.BM
  CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbT CertificateChecks.KernelBM.CTIB
  CertificateChecks.KernelBM.CTIB.CosetQ CertificateChecks.KernelBM.CTIB.Inner

set_option maxRecDepth 400000

namespace CertificateChecks.Batch3136

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.B.GSide CFSG.KC.BM
  CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbT CertificateChecks.KernelBM.CTIB
  CertificateChecks.KernelBM.CTIB.CosetQ CertificateChecks.KernelBM.CTIB.Inner

private theorem yWords_eq :
    yWords = (List.range 6).map fun j => (nthLL Y3136.STs j).flatMap symLetters := by
  decide +kernel

private theorem stY_lt : ∀ j < 6, (nthLL Y3136.STs j).all (· < 17) = true := by decide +kernel

private theorem yFlips_eq : ∀ j < 6, yFlips.getD j 0 = nthN Y3136.Fs j := by decide +kernel

private theorem getD6 (f : ℕ → Array ℕ) {j : ℕ} (hj : j < 6) :
    ((List.range 6).map f).toArray.getD j #[] = f j := by
  simp [hj]

private theorem yAuts_eq : yAuts () = ((List.range 6).map fun j => arrOf (nthN Y3136.Ys j)).toArray := by
  unfold yAuts
  rw [yWords_eq, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hj' := List.mem_range.1 hj
  have hs : ∀ s ∈ nthLL Y3136.STs j, s < 17 := by
    have h := stY_lt j hj'
    rw [List.all_eq_true] at h
    exact fun s hs => of_decide_eq_true (h s hs)
  rw [Function.comp_apply, word_imgs symFacts ct_eq _ hs, beq_iff.1 (Y3136.words j hj')]

private theorem yAct_eq {j : ℕ} (hj : j < 6) (n : ℕ) : yAct (yAuts ()) j n = Y3136.act j n := by
  rw [yAct, yAuts_eq, getD6 _ hj, yFlips_eq j hj, qinv]
  simp only [Y3136.act, yActK, QK.mulQ_eq, QK.autQ_eq]

private theorem qmul_of {a b c : ℕ} (h : Nat.beq (mulQ LOq a b) c = true) : qmul gArr a b = c := by
  rw [← QK.mulQ_eq]
  exact beq_iff.1 h

private theorem ty_of {e n k : ℕ} (hw : walkOK e = true) (hn : Nat.beq (n % 2 ^ 22) (eV e) = true)
    (h0 : Nat.blt 0 (eV e) = true) (hk : Nat.beq (eRec e) k = true) :
    innerTy innerTab n = k + 1 := by
  rw [innerTy_walk KernelBM.census_orbitLists hw (beq_iff.1 hn) (Nat.pos_iff_ne_zero.1 (blt_iff.1 h0)),
    beq_iff.1 hk]

private theorem walk_neg : (!(walkOK (Nat.xor CFSG.KD.Y3136.W0 (Nat.shiftLeft 1 31)))) = true := by
  quickRfl

private theorem ty32 : innerTy innerTab 32 = 1 :=
  ty_of (e := CFSG.KD.Y3136.W0) (k := 0) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)

private theorem ty39 : innerTy innerTab 39 = 3 :=
  ty_of (e := CFSG.KD.Y3136.W1) (k := 2) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)

private theorem ty128 : innerTy innerTab 128 = 1 :=
  ty_of (e := CFSG.KD.Y3136.W2) (k := 0) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)

private theorem tyX : innerTy innerTab 7618823 = 3 :=
  ty_of (e := CFSG.KD.Y3136.W3) (k := 2) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)

private theorem tyC : innerTy innerTab 3424647 = 3 :=
  ty_of (e := CFSG.KD.Y3136.W4) (k := 2) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)

private theorem frame32 : frameA innerTab 32 = true := by
  rw [frameA, qmul_of (c := 39) (by quickRfl), qmul_of (a := 7) (c := 39) (by quickRfl), ty32, ty39]
  rfl

private theorem aut128 : autApply gArr (liftImgsN 8).toArray 128 = 128 := by
  rw [lift8, ← QK.autQ_eq]
  exact beq_iff.1 (by quickRfl)

private theorem sq9 :
    qmul gArr (sqCode 8) (qmul gArr (autApply gArr (liftImgsN 8).toArray 9) 9) = 7618823 := by
  rw [lift8, ← QK.autQ_eq, ← QK.mulQ_eq, ← QK.mulQ_eq]
  exact beq_iff.1 (by quickRfl)

private theorem bfs32 :
    Native.natCertOK (yAct (yAuts ())) 6 (fun p => decide (p < 2 ^ 23)) 32
        (Native.natBfs (yAct (yAuts ())) 6 32 2241).1 (Native.natBfs (yAct (yAuts ())) 6 32 2241).2.1
        (Native.natBfs (yAct (yAuts ())) 6 32 2241).2.2.1
        (Native.natBfs (yAct (yAuts ())) 6 32 2241).2.2.2 = true ∧
      (Native.natBfs (yAct (yAuts ())) 6 32 2241).1.size = 2240 := by
  obtain ⟨hS, hcard, hb⟩ := orbT_reach (fun k hk x => yAct_eq hk x) Y3136.inc Y3136.clos Y3136.tree
    (by decide) (beq_iff.1 Y3136.root)
  obtain ⟨hc, -, hsz⟩ := natBfs_native (valid := fun p => decide (p < 2 ^ 23)) (fuel := 2241) _
    (fun x => reach_bfs.trans (hS x)) (fun x hx => decide_eq_true (Nat.lt_of_lt_of_eq (hb x hx) rfl))
    ((Nat.le_of_eq hcard).trans (by decide))
  exact ⟨hc, hsz.trans hcard⟩

private theorem fix7 : ((List.range 6).all fun j => yAct (yAuts ()) j 7 == 7) = true := by
  rw [List.all_eq_true]
  intro j hj
  rw [yAct_eq (List.mem_range.1 hj), beq_iff_eq]
  exact beq_iff.1 (Y3136.fix7 j (List.mem_range.1 hj))

private theorem y3CertOK_eq_true : y3CertOK innerTab = true := by
  unfold y3CertOK
  simp only [fix7, frame32, bfs32, ty128, aut128, sq9, tyX, tyC,
    qmul_of (a := 128) (b := 9) (c := 137) (by quickRfl), qmul_of (a := 9) (b := 128) (c := 137) (by quickRfl),
    qmul_of (a := 128) (b := 7618823) (c := 3424647) (by quickRfl),
    qmul_of (a := 7618823) (b := 128) (c := 3424647) (by quickRfl), beq_self_eq_true, Bool.and_self]

end CertificateChecks.Batch3136

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.GSide CFSG.Monster.B.CTIB in
theorem certificate3136 : y3CertOK innerTab = true := CertificateChecks.Batch3136.y3CertOK_eq_true

end Certificates

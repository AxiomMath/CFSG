module

public import Certificates.Kernel.Co2I301.RowFive
public import Certificates.Kernel.Co2I301.RowV8
public import Certificates.Kernel.Co2I301.SmallProof
public import CFSG.Certificates.Kernel.Co2I301.SixCentSound
public import CFSG.Certificates.Kernel.SporSch.CentNormAll
public import CFSG.Certificates.Kernel.SporSch.SpanK3Sound
public import CFSG.Certificates.Kernel.SporSch.J1PtSound
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
public import CFSG.Sporadic.Schreier.J1CountCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KC.Co2I301 CFSG.KS CFSG.KS.Raw CFSG.KS.Co2I301 CFSG.KS.MatRep
  CFSG.KS.SpanK CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier CFSG.Certificates.Native
  CFSG.HardMathSupport.Dickson.I271 CFSG.Sporadic.Co2I301
  CFSG.LocalAnalysis.GLTheoremA.H301B.Co2RowNative CFSG.RankThree.PartOne
  CFSG.Sporadic.SmallF2.Native CFSG.Certificates CFSG.RankThree.Native
open CertificateChecks.KernelSporSch.Co2M (cmpP invP powP prodOrZK qT rep_cmp rep_inv rep_pow
  isInvA_rep prodOrZ_of q_len qRep)

theorem r7_of_inv {P Q : ℕ} (h : inv63 P Q = true) : ∃ g : Equiv.Perm (Fin 63), R7 P g := by
  have h' : permOK 63 7 (CFSG.KS.mask 7) (63 * 7) P Q = true := by rw [mask7]; exact h
  exact CFSG.KS.SporSch.MOC.exists_prep h'

theorem rep_orig {g : ℕ} (hg : g < 2) {A : Equiv.Perm (Fin 63)} (hA : R7 (PI g) A) :
    Rep 63 sixRec.origArrs[g]! A := by
  intro x
  have h := beq_true (allN_spec (allN_spec pi_bind g hg) x x.2)
  exact h.symm.trans (r7_apply hA x)

theorem unpack78 : CFSG.KS.Raw.unpack 63 7 XC = CFSG.KS.Raw.unpack 63 8 X8 := by
  apply Array.ext
  · simp [CFSG.KS.Raw.unpack]
  · intro i h1 h2
    have hi : i < 63 := by simpa [CFSG.KS.Raw.unpack] using h1
    have e := allN_spec x8_ok i hi
    rw [Bool.and_eq_true] at e
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, Orb.unpack_get hi, Orb.unpack_get hi,
      beq_true e.1, pt_eq]

theorem x0_eq : compA 63 (perm63Of (i301K1 ())) (perm63Of (i301K2 ())) =
    CFSG.KS.Raw.unpack 63 7 XC := by
  obtain ⟨-, -, h5, h6⟩ := perm63Of_eq
  rw [i301K1_eq, i301K2_eq, h5, h6, compA_unpack63 fun p hp => rng_parts.2.2.2 p hp]
  rfl

theorem d0_eq : perm63Of (i301D ()) = CFSG.KS.Raw.unpack 63 7 SX.fd := perm63Of_eq.1

theorem sixRec_base : sixRec.baseArr = (([0, 1, 3, 7, 15, 31] : List (Fin 63)).map Fin.val).toArray := by
  unfold ChainRecord.baseArr
  change KernelSporSch.Co2M.sixC.base.toArray = _
  rw [KernelSporSch.Co2Six.shapeOK.2.2.2.2]
  rfl

theorem sixRec_size : sixRec.strongArrs.size = 12 := by
  unfold ChainRecord.strongArrs
  simp only [List.size_toArray, List.length_map]
  exact KernelSporSch.Co2Six.shapeOK.1

theorem six_chain : caseChainOK2P 63 sixRec.strongArrs sixRec.baseArr sixRec.wordArrs
    sixRec.origArrs[0]! sixRec.origArrs[1]! = true := by
  have h := rawChainK_sound (chunks := 1) (NS := 1) (CH := 64) KernelSporSch.Co2Six.binds
    KernelSporSch.Co2Six.head KernelSporSch.Co2Six.hl (by norm_num) KernelSporSch.Co2Six.hs
  have hw : sixRec.wordArrs = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 12 KernelSporSch.Co2M.sixD :=
    wordArrs_eq KernelSporSch.Co2Six.shapeOK.2.1 (by
      have h10 := KernelSporSch.Co2Six.shapeOK.2.2.1
      change KernelSporSch.Co2M.sixC.derivations.length + 2 = 12
      omega)
  have ho : sixRec.origArrs = sixRec.strongArrs.extract 0 2 :=
    origArrs_eq KernelSporSch.Co2Six.shapeOK.2.2.2.1
  have hF := chainCheckFacts h
  have hs : (sixRec.strongArrs.extract 0 2).size = 2 := by simp [sixRec_size]
  have i0 : eqA 63 sixRec.strongArrs[0]! (sixRec.strongArrs.extract 0 2)[0]! = true :=
    hF.initial 0 (by change 0 < (sixRec.strongArrs.extract 0 2).size; rw [hs]; norm_num)
  have i1 : eqA 63 sixRec.strongArrs[1]! (sixRec.strongArrs.extract 0 2)[1]! = true :=
    hF.initial 1 (by change 1 < (sixRec.strongArrs.extract 0 2).size; rw [hs]; norm_num)
  unfold caseChainOK2P
  rw [hw, ho]
  change rawChainOK 63 (sixRec.strongArrs.extract 0 2) sixRec.strongArrs sixRec.baseArr
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 12 KernelSporSch.Co2M.sixD) 1 = true at h
  rw [h, i0, i1]
  rfl

theorem six_x0_check : sixX0Check () = true := by
  obtain ⟨A, hA⟩ := r7_of_inv inv_parts.1
  obtain ⟨B, hB⟩ := r7_of_inv inv_parts.2.1
  have hi := inv5_ok
  rw [Bool.and_eq_true] at hi
  obtain ⟨X, hX⟩ := r7_of_inv hi.1
  obtain ⟨D, hD⟩ := r7_of_inv hi.2
  have rK1 : MatRep.Rep 22 co2PackedVecs (i301K1 ()) (rowP 5).1 (rowP 5).2 := by
    rw [i301K1_eq]
    exact rep_arr 5 (by norm_num)
  have rK2 : MatRep.Rep 22 co2PackedVecs (i301K2 ()) (rowP 6).1 (rowP 6).2 := by
    rw [i301K2_eq]
    exact rep_arr 6 (by norm_num)
  have hpow : eqA 2300 (powArr 2300 (compA 2300 (i301K1 ()) (i301K2 ())) 5) (idA 2300) = true :=
    eqId_of_mat (rep_pow (rep_cmp rK1 rK2) 5) pow5_ok
  have hx : Rep 63 (compA 63 (perm63Of (i301K1 ())) (perm63Of (i301K2 ()))) X := by
    rw [x0_eq]
    exact Orb.rep_unpack hX
  have hrD : Rep 63 (perm63Of (i301D ())) D := by
    rw [d0_eq]
    exact Orb.rep_unpack hD
  have hsx : siftA 63 (rawLevels 63 sixRec.strongArrs sixRec.baseArr) sixRec.baseArr 0
      (compA 63 (perm63Of (i301K1 ())) (perm63Of (i301K2 ()))) = true := by
    have hr : allN 63 (fun i => Nat.blt (pg 8 (CFSG.KS.mask 8) X8 i) 63) = true := by
      rw [Orb.allN_iff]
      intro i hi
      have e := allN_spec x8_ok i hi
      rw [Bool.and_eq_true] at e
      exact e.2
    rw [x0_eq, unpack78]
    exact Orb.siftA_of_K KernelSporSch.Co2Six.binds KernelSporSch.Co2Six.perm KernelSporSch.Co2Six.hl
      rfl hr sift5_ok
  have hcent := sixCentK_sound hA hB hX hD cent5_ok
  have hT : ∀ (t : Array ℕ) (G : Equiv.Perm (Fin 63)), Rep 63 t G →
      G ∈ Subgroup.closure {A, B} → G * X = X * G → leafD3 (perm63Of (i301D ())) t = true := by
    intro t G ht hG hc
    unfold leafD3
    by_cases h3 : G * (G * G) = 1
    · have h3' : G ^ 3 = 1 := by
        rw [pow_three]
        exact h3
      rcases hcent G hG hc h3' with rfl | rfl | rfl
      · rw [(eqA_iff ht rep_idA).2 rfl]
        simp
      · rw [(eqA_iff ht hrD).2 rfl]
        simp
      · rw [(eqA_iff ht (rep_compA hrD hrD)).2 rfl]
        simp
    · have hf : eqA 63 (compA 63 t (compA 63 t t)) (idA 63) = false := by
        cases e : eqA 63 (compA 63 t (compA 63 t t)) (idA 63)
        · rfl
        · exact absurd ((eqA_iff (rep_compA ht (rep_compA ht ht)) rep_idA).1 e) h3
      rw [hf]
      rfl
  have hcn := centNormMemOKP_nil_of_all (p := 5) (S := sixRec.strongArrs) (by norm_num)
    (by rw [sixRec_size]; norm_num)
    (bs := [0, 1, 3, 7, 15, 31]) (by decide) sixRec_base (rep_orig (by norm_num) hA)
    (rep_orig (by norm_num) hB) six_chain hx hsx (M := fun _ => true) hT
  unfold sixX0Check
  dsimp only
  rw [hpow, six_chain, hcn]
  rfl

theorem cols_of {g : Array ℕ} {p : ℕ × ℕ} (hg : MatRep.Rep 22 co2PackedVecs g p.1 p.2)
    {cols : Array ℕ} (h : colsK p cols = true) : conjColsOK g cols = true := by
  have hv : validA 2300 g = true := isInvA_rep hg
  unfold conjColsOK
  rw [hv, isInvA_rep hg, Bool.true_and, Bool.true_and]
  unfold colsK at h
  rw [CFSG.Monster.B.Co2.allLt_iff] at h ⊢
  intro l hl
  have hl' := h l hl
  rw [Bool.and_eq_true] at hl' ⊢
  exact ⟨hl'.1, prodOrZ_of (rep_cmp (rep_cmp hg (repT_get qRep (by rw [q_len]; exact hl)))
    (rep_inv hg)) _ hl'.2⟩

theorem span_ok (v : ℕ) (hv : v < 255) : Nat.beq (iterK3 (tabK (RT 0)) (tabK (RT 1))
    (tabK (RT 2)) 5 (insK 1 (Nat.succ v))) (Nat.sub (Nat.shiftLeft 1 256) 1) = true := by
  have hc : ∀ s < 16, ∀ t < 16, spanR (Nat.add (16 * s) t) = true := by
    intro s hs t ht
    interval_cases s
    exacts [allN_spec spanR0 t ht, allN_spec spanR1 t ht, allN_spec spanR2 t ht,
      allN_spec spanR3 t ht, allN_spec spanR4 t ht, allN_spec spanR5 t ht, allN_spec spanR6 t ht,
      allN_spec spanR7 t ht, allN_spec spanR8 t ht, allN_spec spanR9 t ht, allN_spec spanR10 t ht,
      allN_spec spanR11 t ht, allN_spec spanR12 t ht, allN_spec spanR13 t ht,
      allN_spec spanR14 t ht, allN_spec spanR15 t ht]
  have h := hc (v / 16) (by omega) (v % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (16 * (v / 16)) (v % 16) = v := Nat.div_add_mod v 16
  rw [e] at h
  have hb : Nat.blt v 255 = true := by rw [Nat.blt_eq]; exact hv
  unfold spanR at h
  rw [hb, Bool.cond_true] at h
  exact h

theorem spanIterL_ok : allLt 255 (fun v => spanIterL [co2K1Cols, co2K2Cols, co2DCols] 5
    (spanIns 1 (v + 1)) == 2 ^ 256 - 1) = true := by
  have ht := tab8_ok
  have hf : ∀ a < 256, tabK (RT 0) a = vecMulN 8 co2K1Cols a ∧
      tabK (RT 1) a = vecMulN 8 co2K2Cols a ∧ tabK (RT 2) a = vecMulN 8 co2DCols a := fun a ha => by
    have := allN_spec ht a ha
    simp only [Bool.and_eq_true] at this
    exact ⟨beq_true this.1.1, beq_true this.1.2, beq_true this.2⟩
  have hs : Nat.sub (Nat.shiftLeft 1 256) 1 = 2 ^ 256 - 1 := by rfl
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro v hv
  have hk := beq_true (span_ok v hv)
  rw [iterK3_eq (fun a ha => (hf a ha).1) (fun a ha => (hf a ha).2.1) (fun a ha => (hf a ha).2.2),
    insK_eq, hs] at hk
  rw [hk]
  exact beq_self_eq_true _

theorem v8_check : v8Check () = true := by
  have hc := cols8_ok
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have rK1 : MatRep.Rep 22 co2PackedVecs (i301K1 ()) (rowP 5).1 (rowP 5).2 := by
    rw [i301K1_eq]
    exact rep_arr 5 (by norm_num)
  have rK2 : MatRep.Rep 22 co2PackedVecs (i301K2 ()) (rowP 6).1 (rowP 6).2 := by
    rw [i301K2_eq]
    exact rep_arr 6 (by norm_num)
  have rD : MatRep.Rep 22 co2PackedVecs (i301D ()) (rowP 1).1 (rowP 1).2 := rep_arr 1 (by norm_num)
  unfold v8Check
  rw [cols_of rK1 h1, cols_of rK2 h2, cols_of rD h3, spanIterL_ok]
  rfl

theorem row_check : co2RowCheck () = true := by
  unfold co2RowCheck
  rw [six_x0_check, v8_check]
  rfl

end CertificateChecks.KernelCo2I301

end

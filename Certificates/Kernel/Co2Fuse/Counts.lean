module

public import Certificates.Kernel.Co2Fuse.Checks
public import Certificates.Kernel.Co2Fuse.RepCheck
public import Certificates.Kernel.Co2Syl.Facts
public import Certificates.Kernel.Co2Cls.Classes
public import Certificates.Kernel.Co2Census.Facts
public import CFSG.Certificates.Kernel.Co2Fuse.Sound
public import CFSG.RankThree.Co2.FuseCounts
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.Co2Fuse

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2Fuse CFSG.RankThree.Co2
  CertificateChecks.KernelSpor.Co2Syl

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

@[expose] def CmCensus : Prop := ∀ x ∈ Cm, x * x = 1 → x ≠ 1 → ∃ i < 10, CrConj (repMat i) x

theorem isUnit_Cm : ∀ g ∈ (Cm : Set M22), IsUnit g := by
  intro g hg
  rw [SetLike.mem_coe, CertificateChecks.KernelSpor.Co2TInv.Cm_eq] at hg
  exact CertificateChecks.KernelSpor.Co2Cls.isUnit_C g hg

theorem cent_r : ∀ g ∈ (Cm : Set M22), g * repMat 0 = repMat 0 * g := by
  intro g hg
  rw [SetLike.mem_coe, CertificateChecks.KernelSpor.Co2TInv.Cm_eq] at hg
  rw [repMat_eq (by norm_num)]
  unfold genMonN at hg
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨j, hj⟩, rfl⟩ := hx
    exact commK_sound (CertificateChecks.KernelSpor.Co2Cls.cent0 j hj)
  | one => rw [one_mul, mul_one]
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

theorem rep_mem_Cm {i : ℕ} (hi : i < 10) : repMat i ∈ Cm := by
  rw [repMat_eq hi, CertificateChecks.KernelSpor.Co2TInv.Cm_eq]
  exact CertificateChecks.KernelSpor.Co2Cls.repMat_mem hi

theorem P3_le_Cm : matGrp pWords3 ≤ Cm := by
  rw [CertificateChecks.KernelSpor.Co2TInv.Cm_eq]
  exact CertificateChecks.KernelSpor.Co2Cls.matGrp_le pWords3_size pWords3_lt

@[expose] def Lf (i : ℕ) : ℕ := fld(LR, Nat.mul 4 i, 15)

theorem Lf_ne : ∀ i < 10, Lf i ≠ 5 := by decide

theorem labM_rep {i : ℕ} (hi : i < 10) : labM (repMat 0) (repMat i) = Lf i := by
  have h := Nat.eq_of_beq_eq_true (repLabs i hi)
  have h5 : labY CR (RP 0) (RP i) (Nat.mul 3 i) ≠ 5 := by
    rw [h]
    exact Lf_ne i hi
  rw [repMat_eq (by norm_num), repMat_eq hi, ← labY_sound (RP_lt hi) h5]
  exact h

theorem inCls_iff (hcen : CmCensus) {S V : Finset ℕ} (hS : ∀ c ∈ S, c < 10)
    (hSV : ∀ c < 10, c ∈ S ↔ Lf c ∈ V) (hV : 0 ∉ V) {x : M22} (hx : x ∈ Cm) :
    InCls S x ↔ labM (repMat 0) x ∈ V := by
  have e := labM_iff (C := (Cm : Set M22)) isUnit_Cm cent_r (reps := repMat) (L := Lf)
    (fun i hi => labM_rep hi) hcen (V := (V : Set ℕ)) (by simpa using hV) hx
  rw [Finset.mem_coe] at e
  rw [← e]
  unfold InCls CrConj
  constructor
  · rintro ⟨c, hc, g, hg, eg⟩
    exact ⟨c, hS c hc, by simpa using (hSV c (hS c hc)).1 hc, g, hg, eg⟩
  · rintro ⟨c, hc, hcV, g, hg, eg⟩
    exact ⟨c, (hSV c hc).2 (by simpa using hcV), g, hg, eg⟩

theorem card_P3 (hc : Nat.card (matGrp pWords3) ≤ 2 ^ 16) : Nat.card (genMon G3) ≤ 65536 := by
  rw [genMon3]
  exact hc

theorem totals : ∀ j < 3, cntTotal CNT j 16 =
    ∑ k ∈ Finset.range 65536, hitR E3.CF (RP 0) (RP 2) 65536 j k :=
  (fuse_total (hi := 16) (by norm_num) fuses).1

theorem card_j (hc : Nat.card (matGrp pWords3) ≤ 2 ^ 16) {j : ℕ} (hj : j < 3) :
    Nat.card {x : M22 // x ∈ matGrp pWords3 ∧ labM (repMat 0) x = 1 ∧
      pairJ j (labM (repMat 0) (x * repMat 0)) (labM (repMat 0) (x * repMat 2))} =
      cntTotal CNT j 16 := by
  rw [totals j hj, ← fuse_card tree3 (card_P3 hc) (RP 0) (RP 2) j, genMon3,
    repMat_eq (j := 0) (by norm_num), repMat_eq (j := 2) (by norm_num)]

theorem inCls_A (hcen : CmCensus) {x : M22} (hx : x ∈ Cm) :
    InCls {0, 2, 7} x ↔ labM (repMat 0) x = 1 := by
  rw [inCls_iff hcen (V := {1}) (by decide) (by decide) (by decide) hx, Finset.mem_singleton]

theorem inCls_C (hcen : CmCensus) {x : M22} (hx : x ∈ Cm) :
    InCls {4, 6, 8} x ↔ labM (repMat 0) x = 3 := by
  rw [inCls_iff hcen (V := {3}) (by decide) (by decide) (by decide) hx, Finset.mem_singleton]

theorem inCls_9 (hcen : CmCensus) {x : M22} (hx : x ∈ Cm) :
    InCls {9} x ↔ labM (repMat 0) x = 4 := by
  rw [inCls_iff hcen (V := {4}) (by decide) (by decide) (by decide) hx, Finset.mem_singleton]

theorem inCls_B9 (hcen : CmCensus) {x : M22} (hx : x ∈ Cm) :
    InCls {1, 3, 5, 9} x ↔ labM (repMat 0) x = 2 ∨ labM (repMat 0) x = 4 := by
  rw [inCls_iff hcen (V := {2, 4}) (by decide) (by decide) (by decide) hx, Finset.mem_insert,
    Finset.mem_singleton]

theorem mem_r {x : M22} (hx : x ∈ matGrp pWords3) : x ∈ Cm ∧ x * repMat 0 ∈ Cm ∧
    x * repMat 2 ∈ Cm :=
  ⟨P3_le_Cm hx, Cm.mul_mem (P3_le_Cm hx) (rep_mem_Cm (by norm_num)),
    Cm.mul_mem (P3_le_Cm hx) (rep_mem_Cm (by norm_num))⟩

theorem fuseN_eq (hcen : CmCensus) (hc : Nat.card (matGrp pWords3) ≤ 2 ^ 16) {S₂ S₃ : Finset ℕ}
    {j : ℕ} (hj : j < 3)
    (h : ∀ x : M22, x ∈ matGrp pWords3 → (InCls S₂ (x * repMat 0) ∧ InCls S₃ (x * repMat 2) ↔
      pairJ j (labM (repMat 0) (x * repMat 0)) (labM (repMat 0) (x * repMat 2)))) :
    fuseN {0, 2, 7} S₂ S₃ = cntTotal CNT j 16 := by
  rw [← card_j hc hj]
  unfold fuseN
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  constructor
  · rintro ⟨hx, h1, h23⟩
    exact ⟨hx, (inCls_A hcen (mem_r hx).1).1 h1, (h x hx).1 h23⟩
  · rintro ⟨hx, h1, h23⟩
    exact ⟨hx, (inCls_A hcen (mem_r hx).1).2 h1, (h x hx).2 h23⟩

theorem fuse_counts (hcen : CmCensus) (hc : Nat.card (matGrp pWords3) ≤ 2 ^ 16) :
    fuseN {0, 2, 7} {4, 6, 8} {9} = 32 ∧ fuseN {0, 2, 7} {9} {4, 6, 8} = 0 ∧
      fuseN {0, 2, 7} {4, 6, 8} {1, 3, 5, 9} = 68 ∧ fuseN {0, 2, 7} {1, 3, 5, 9} {4, 6, 8} = 36 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fuseN_eq hcen hc (j := 0) (by norm_num) fun x hx => ?_, Nat.eq_of_beq_eq_true totC9]
    rw [inCls_C hcen (mem_r hx).2.1, inCls_9 hcen (mem_r hx).2.2]
    simp [pairJ]
  · unfold fuseN
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨x, hx, h1, h2, h3⟩ => ?_⟩
    have hx' : x ∈ genMon G3 := by rw [genMon3]; exact hx
    refine fuse_none tree3 (card_P3 hc) (R := RP 0) (S := RP 2)
      (fuse_total (hi := 16) (by norm_num) fuses).2 x hx' ?_
    rw [← repMat_eq (j := 0) (by norm_num), ← repMat_eq (j := 2) (by norm_num)]
    exact ⟨(inCls_A hcen (mem_r hx).1).1 h1, (inCls_9 hcen (mem_r hx).2.1).1 h2,
      (inCls_C hcen (mem_r hx).2.2).1 h3⟩
  · rw [fuseN_eq hcen hc (j := 1) (by norm_num) fun x hx => ?_, Nat.eq_of_beq_eq_true totCB9]
    rw [inCls_C hcen (mem_r hx).2.1, inCls_B9 hcen (mem_r hx).2.2]
    simp [pairJ]
  · rw [fuseN_eq hcen hc (j := 2) (by norm_num) fun x hx => ?_, Nat.eq_of_beq_eq_true totB9C]
    rw [inCls_B9 hcen (mem_r hx).2.1, inCls_C hcen (mem_r hx).2.2]
    simp [pairJ]

end CertificateChecks.KernelSpor.Co2Fuse

end

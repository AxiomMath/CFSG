module

public import Certificates.Kernel.Co2I301.Bridge63
public import Certificates.Kernel.Co2I301.SixChk
public import CFSG.Certificates.Kernel.Co2I301.SixSound
public import CFSG.Sporadic.Co2Schreier.SixGroup
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
public import Certificates.Kernel.Co2I301.Mats

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KC.Co2I301 CFSG.KS CFSG.KS.Co2I301 CFSG.KS.Raw.Orb CFSG.KS.MatRep
  CFSG.Sporadic.Co2I301 CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem pi_bind : allN 2 (fun g => allN 63 (fun p =>
    Nat.beq (pt (PI g) p) ((witRec.wLocal.sixActionChain.origArrs[g]!)[p]!))) = true := by
  decide +kernel

theorem cols_ok : (colsOKK (M 1) && colsOKK (M 2) && colsOKK (M 5) && colsOKK (M 6)) = true := by
  decide +kernel

theorem p63_ok : (allN 63 (fun p => Nat.beq (pt SX.fd p) (p63K (M 1) p)) &&
    allN 63 (fun p => Nat.beq (pt SX.fs p) (p63K (M 2) p)) &&
    allN 63 (fun p => Nat.beq (pt SX.fk1 p) (p63K (M 5) p)) &&
    allN 63 (fun p => Nat.beq (pt SX.fk2 p) (p63K (M 6) p))) = true := by
  decide +kernel

theorem rng_ok : (allN 63 (fun p => Nat.blt (pt SX.fd p) 63) &&
    allN 63 (fun p => Nat.blt (pt SX.fs p) 63) && allN 63 (fun p => Nat.blt (pt SX.fk1 p) 63) &&
    allN 63 (fun p => Nat.blt (pt SX.fk2 p) 63)) = true := by
  decide +kernel

@[expose] noncomputable def FL (i : Nat) : Nat := [SX.fk1, SX.fk2, SX.fd].getD i 0

@[expose] noncomputable def wF (w : List Nat) : Nat := w.foldl (fun acc i => cp acc (FL i)) idc

theorem hlw_ok : allN 3 (fun t => Nat.beq (HL t) (wF (hlWords.getD t []))) = true := by
  decide +kernel

theorem r7_PI {g : ℕ} (hg : g < 2) : R7 (PI g) (sixPi g) := by
  intro x
  have h := beq_true (allN_spec (allN_spec pi_bind g hg) x x.2)
  change pg 7 (CFSG.KS.mask 7) (PI g) x = _
  rw [← pt_eq, h]
  exact rep_sixPi hg x

theorem inv_parts : inv63 (PI 0) (PII 0) = true ∧ inv63 (PI 1) (PII 1) = true ∧
    inv63 (HL 0) (HLI 0) = true ∧ inv63 (HL 1) (HLI 1) = true ∧ inv63 (HL 2) (HLI 2) = true := by
  have h := inv_ok
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem r7_PII {g : ℕ} (hg : g < 2) : R7 (PII g) (sixPi g)⁻¹ := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · exact r7_inv (r7_PI (by norm_num)) inv_parts.1
  · exact r7_inv (r7_PI (by norm_num)) inv_parts.2.1

theorem p63_parts : (∀ p < 63, pt SX.fd p = p63K (M 1) p) ∧ (∀ p < 63, pt SX.fs p = p63K (M 2) p) ∧
    (∀ p < 63, pt SX.fk1 p = p63K (M 5) p) ∧ (∀ p < 63, pt SX.fk2 p = p63K (M 6) p) := by
  have h := p63_ok
  simp only [Bool.and_eq_true] at h
  exact ⟨fun p hp => beq_true (allN_spec h.1.1.1 p hp), fun p hp => beq_true (allN_spec h.1.1.2 p hp),
    fun p hp => beq_true (allN_spec h.1.2 p hp), fun p hp => beq_true (allN_spec h.2 p hp)⟩

theorem rng_parts : (∀ p < 63, pt SX.fd p < 63) ∧ (∀ p < 63, pt SX.fs p < 63) ∧
    (∀ p < 63, pt SX.fk1 p < 63) ∧ (∀ p < 63, pt SX.fk2 p < 63) := by
  have h := rng_ok
  simp only [Bool.and_eq_true] at h
  exact ⟨fun p hp => blt_true (allN_spec h.1.1.1 p hp), fun p hp => blt_true (allN_spec h.1.1.2 p hp),
    fun p hp => blt_true (allN_spec h.1.2 p hp), fun p hp => blt_true (allN_spec h.2 p hp)⟩

theorem cols_parts : colsOKK (M 1) = true ∧ colsOKK (M 2) = true ∧ colsOKK (M 5) = true ∧
    colsOKK (M 6) = true := by
  have h := cols_ok
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem unpack63_get {F p : ℕ} (hp : p < 63) : (CFSG.KS.Raw.unpack 63 7 F)[p]! = pt F p := by
  rw [unpack_get hp, pt_eq]

theorem unpack63_size (F : ℕ) : (CFSG.KS.Raw.unpack 63 7 F).size = 63 := by
  simp [CFSG.KS.Raw.unpack]

theorem eq_unpack63 {a : Array ℕ} {F : ℕ} (hs : a.size = 63) (h : ∀ p < 63, a[p]! = pt F p) :
    a = CFSG.KS.Raw.unpack 63 7 F := by
  apply Array.ext
  · rw [hs, unpack63_size]
  · intro i h1 h2
    rw [hs] at h1
    have e1 := h i h1
    rw [getElem!_pos a i (by omega)] at e1
    rw [e1, ← unpack63_get h1, getElem!_pos _ i (by rw [unpack63_size]; exact h1)]

theorem perm63Of_size (t : Array ℕ) : (perm63Of t).size = 63 := by simp [perm63Of]

theorem perm63Of_eq : perm63Of (i301Arr 1) = CFSG.KS.Raw.unpack 63 7 SX.fd ∧
    perm63Of (i301Arr 2) = CFSG.KS.Raw.unpack 63 7 SX.fs ∧
    perm63Of (i301Arr 5) = CFSG.KS.Raw.unpack 63 7 SX.fk1 ∧
    perm63Of (i301Arr 6) = CFSG.KS.Raw.unpack 63 7 SX.fk2 := by
  obtain ⟨h1, h2, h5, h6⟩ := p63_parts
  refine ⟨eq_unpack63 (perm63Of_size _) fun p hp => ?_, eq_unpack63 (perm63Of_size _) fun p hp => ?_,
    eq_unpack63 (perm63Of_size _) fun p hp => ?_, eq_unpack63 (perm63Of_size _) fun p hp => ?_⟩
  · rw [perm63Of_get (rep_arr 1 (by norm_num)) hp, h1 p hp]
  · rw [perm63Of_get (rep_arr 2 (by norm_num)) hp, h2 p hp]
  · rw [perm63Of_get (rep_arr 5 (by norm_num)) hp, h5 p hp]
  · rw [perm63Of_get (rep_arr 6 (by norm_num)) hp, h6 p hp]

theorem sixColsOK_arr : sixColsOK (i301Arr 1) = true ∧ sixColsOK (i301Arr 2) = true ∧
    sixColsOK (i301Arr 5) = true ∧ sixColsOK (i301Arr 6) = true := by
  obtain ⟨h1, h2, h5, h6⟩ := cols_parts
  rw [sixColsOK_eq (rep_arr 1 (by norm_num)), sixColsOK_eq (rep_arr 2 (by norm_num)),
    sixColsOK_eq (rep_arr 5 (by norm_num)), sixColsOK_eq (rep_arr 6 (by norm_num))]
  exact ⟨h1, h2, h5, h6⟩

theorem compA_unpack63 {a b : ℕ} (hb : ∀ p < 63, pt b p < 63) :
    compA 63 (CFSG.KS.Raw.unpack 63 7 a) (CFSG.KS.Raw.unpack 63 7 b) =
      CFSG.KS.Raw.unpack 63 7 (cp a b) := by
  refine eq_unpack63 (by simp [compA]) fun p hp => ?_
  rw [compA_get hp, unpack63_get hp, unpack63_get (hb p hp), pt_eq, pt_eq, pt_eq, cp_eq,
    PF.pg_pcomp (by norm_num) hp]

theorem idA_unpack63 : idA 63 = CFSG.KS.Raw.unpack 63 7 idc := by
  refine eq_unpack63 (by simp [idA]) fun p hp => ?_
  rw [idA_get hp, pt_eq]
  exact (PF.pg_pidn (by norm_num) (by norm_num) hp).symm

theorem FL_lt {i p : ℕ} (hi : i < 3) (hp : p < 63) : pt (FL i) p < 63 := by
  obtain ⟨h1, -, h5, h6⟩ := rng_parts
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact h5 p hp
  · exact h6 p hp
  · exact h1 p hp

theorem word63_unpack (w : List ℕ) (hw : ∀ i ∈ w, i < 3) :
    word63 #[CFSG.KS.Raw.unpack 63 7 SX.fk1, CFSG.KS.Raw.unpack 63 7 SX.fk2,
      CFSG.KS.Raw.unpack 63 7 SX.fd] w = CFSG.KS.Raw.unpack 63 7 (wF w) := by
  unfold word63 wF
  rw [idA_unpack63]
  generalize idc = a
  induction w generalizing a with
  | nil => rfl
  | cons i w ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have hi := hw i List.mem_cons_self
    have e : (#[CFSG.KS.Raw.unpack 63 7 SX.fk1, CFSG.KS.Raw.unpack 63 7 SX.fk2,
        CFSG.KS.Raw.unpack 63 7 SX.fd] : Array (Array ℕ))[i]! = CFSG.KS.Raw.unpack 63 7 (FL i) := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
    rw [e, compA_unpack63 fun p hp => FL_lt hi hp]
    exact ih (fun j hj => hw j (List.mem_cons_of_mem _ hj)) _

theorem hlWords_lt : ∀ w ∈ hlWords, ∀ i ∈ w, i < 3 := by decide

theorem hl63_size : (hl63 ()).size = 3 := by simp [hl63, hlWords]

theorem i301K1_eq : i301K1 () = i301Arr 5 := by simp [i301K1, k0Arrs]

theorem i301K2_eq : i301K2 () = i301Arr 6 := by simp [i301K2, k0Arrs]

theorem hl63_get {t : ℕ} (ht : t < 3) : (hl63 ())[t]! = CFSG.KS.Raw.unpack 63 7 (HL t) := by
  have e1 := i301K1_eq
  have e2 := i301K2_eq
  have e3 : i301D () = i301Arr 1 := rfl
  obtain ⟨p1, -, p5, p6⟩ := perm63Of_eq
  have hw : (hl63 ())[t]! = word63 #[CFSG.KS.Raw.unpack 63 7 SX.fk1,
      CFSG.KS.Raw.unpack 63 7 SX.fk2, CFSG.KS.Raw.unpack 63 7 SX.fd] (hlWords.getD t []) := by
    rw [hl63, e1, e2, e3, p1, p5, p6, getElem!_pos _ t (by simpa [hlWords] using ht)]
    simp [List.getD_eq_getElem?_getD, hlWords]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;> rfl
  rw [hw, word63_unpack _ fun i hi => hlWords_lt _ (getD_mem (by simpa [hlWords] using ht)) i hi,
    ← beq_true (allN_spec hlw_ok t ht)]

theorem r7_HL {t : ℕ} (ht : t < 3) : R7 (HL t) (permOfArr 63 (hl63 ())[t]!) := by
  have hinv : inv63 (HL t) (HLI t) = true := by
    obtain ⟨-, -, h0, h1, h2⟩ := inv_parts
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
    exacts [h0, h1, h2]
  have h' : permOK 63 7 (CFSG.KS.mask 7) (63 * 7) (HL t) (HLI t) = true := by
    rw [mask7]
    exact hinv
  rw [hl63_get ht]
  exact prep_of_rep (rep_permOfArr (isInvA_unpack h')).1

theorem r7_HLI {t : ℕ} (ht : t < 3) : R7 (HLI t) (permOfArr 63 (hl63 ())[t]!)⁻¹ := by
  obtain ⟨-, -, h0, h1, h2⟩ := inv_parts
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  exacts [r7_inv (r7_HL (by norm_num)) h0, r7_inv (r7_HL (by norm_num)) h1,
    r7_inv (r7_HL (by norm_num)) h2]

end CertificateChecks.KernelCo2I301

end

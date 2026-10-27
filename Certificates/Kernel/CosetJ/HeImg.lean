module

public import Certificates.Data.HePresImage
public import Certificates.Kernel.CosetJ.HeImgData
public import Certificates.Kernel.CosetJ.HeImgLit
public import Certificates.Kernel.Sporadic.He.Rels
public import Certificates.Kernel.Sporadic.OrdCommon
import Certificates.Kernel.CosetJ.HeImgStr
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Certificates.Kernel.Sporadic.ON.Gen
import all Certificates.Data.HePresData
import all Certificates.Data.HePresCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCosetJ.HeImg

open CFSG.KC.Ord CFSG.KS.Ord CFSG.ComponentClassification.AS81.HePres.Native
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native

open CertificateChecks.KernelCosetJ.HeImgStr in
noncomputable def gw : List (List ℤ) :=
  List.map (fun cs => cs.map fun c : Char =>
      if c = 'a' then (1 : ℤ) else if c = 'A' then -1 else if c = 'b' then 2 else -2)
    [W0, W1, W2, W3, W4, W5, W6, W7]

open CertificateChecks.KernelCosetJ.HeImgStr in
theorem gw_eq : hePiHeWords = gw := by
  unfold hePiHeWords seedLetters
  simp only [List.map_cons, List.map_nil]
  rw [w0_toList, w1_toList, w2_toList, w3_toList, w4_toList, w5_toList, w6_toList, w7_toList]
  rfl

def seedLet (l : ℤ) : ℕ × Bool :=
  if l = 1 ∨ l = -1 then (0, true) else if l = 2 then (1, true) else (1, false)

def piLet (l : Fin 8 × Bool) : ℕ × Bool := (2 + l.1.val, l.2)

def chunk (w : List ℤ) (t : ℕ) : List ℤ := (w.drop (128 * t)).take 128

theorem rels_len : rels.length = 216 := by decide +kernel

theorem relsC : ∀ i < 8, ∀ t < 22, rels.getD (22 * i + t) [] =
    (11 + 22 * i + t, false) :: (chunk (hePiHeWords.getD i []) t).map seedLet := by
  rw [gw_eq]
  decide +kernel

theorem relsW : ∀ i < 8, rels.getD (176 + i) [] =
    (2 + i, false) :: (List.range 22).map fun t => (11 + 22 * i + t, true) := by decide +kernel

theorem relsPi : (rels.drop 184).take 28 = hePiRels.map (List.map piLet) := by decide +kernel

theorem relsT : rels.drop 212 = [(0, false) :: hePiAWord.map piLet,
    (1, false) :: hePiBWord.map piLet, (10, false) :: heT1Letters.map seedLet,
    (10, false) :: hePiZWord.map piLet] := by decide +kernel

theorem flat : ∀ i < 8, ((List.range 22).map (chunk (hePiHeWords.getD i []))).flatten =
    hePiHeWords.getD i [] := by
  rw [gw_eq]
  decide +kernel

theorem gw_letters : (hePiHeWords.length = 8) ∧ ∀ w ∈ hePiHeWords, lettersOK 2 w = true := by
  rw [gw_eq]
  decide +kernel

theorem rb1 : Nat.beq (CFSG.KD.CJHeImg.RB 1) (CFSG.KD.OrdHe.RH 1) = true := by quickRfl
theorem rb2 : Nat.beq (CFSG.KD.CJHeImg.RB 2) (CFSG.KD.OrdHe.RH 2) = true := by quickRfl

theorem hroots : rootsOK CFSG.KD.CJHeImg.RB
    (validM (nat_lit 7) (nat_lit 30000) CFSG.KD.OrdHe.L CFSG.KD.OrdHe.H) (nat_lit 1)
    (nat_lit 188) = true := by quickRfl

theorem hinv : invsOK CFSG.KD.CJHeImg.RB
    (mulR (nat_lit 7) (nat_lit 12) (nat_lit 600) (nat_lit 50) (nat_lit 8) CFSG.KD.OrdHe.L
      CFSG.KD.OrdHe.H CFSG.KD.OrdHe.CM CFSG.KD.OrdHe.RM)
    (validM (nat_lit 7) (nat_lit 30000) CFSG.KD.OrdHe.L CFSG.KD.OrdHe.H) (nat_lit 187)
    CFSG.KD.OrdHe.ONE = true := by quickRfl

theorem relB : relsBounded rels (nat_lit 187) = true := by quickRfl

theorem relN : Nat.beq (lenRels rels) (nat_lit 216) = true := by quickRfl

@[expose] noncomputable def relF (k : ℕ) : Bool := relOK CFSG.KD.CJHeImg.RB
    (mulR (nat_lit 7) (nat_lit 12) (nat_lit 600) (nat_lit 50) (nat_lit 8) CFSG.KD.OrdHe.L
      CFSG.KD.OrdHe.H CFSG.KD.OrdHe.CM CFSG.KD.OrdHe.RM) rels (nat_lit 187)
    CFSG.KD.OrdHe.ONE k

abbrev relK (k : ℕ) : Prop := relF k = true

#kon_slices CertificateChecks.KernelCosetJ.HeImg.relF 0 216
#kon_join CertificateChecks.KernelCosetJ.HeImg.relAll
  CertificateChecks.KernelCosetJ.HeImg.relF 216

theorem allRel {r : ℕ} (hr : r < 216) : relK r := relAll r hr

noncomputable abbrev X (g : ℕ) : Matrix (Fin 50) (Fin 50) (ZMod 7) :=
  ordMat 7 50 12 600 (CFSG.KD.CJHeImg.RB g)

theorem hom : (∀ g < 187, X (g + 1) * X (187 + 1 + g) = 1) ∧
    ∀ v ∈ rels, (v.map fun x => ordMat 7 50 12 600 (letM CFSG.KD.CJHeImg.RB 187 x)).prod = 1 := by
  refine rels_sound (hnb := rfl) CFSG.KD.OrdHe.consts hroots hinv relB fun r hr => Or.inl ?_
  rw [Nat.eq_of_beq_eq_true relN] at hr
  exact allRel hr

noncomputable abbrev Y (x : ℕ × Bool) : Matrix (Fin 50) (Fin 50) (ZMod 7) :=
  ordMat 7 50 12 600 (letM CFSG.KD.CJHeImg.RB 187 x)

theorem Y_true (g : ℕ) : Y (g, true) = X (g + 1) := rfl

theorem Y_false (g : ℕ) : Y (g, false) = X (187 + 1 + g) := rfl

theorem rel_one {v : List (ℕ × Bool)} (hv : v ∈ rels) : (v.map Y).prod = 1 := hom.2 v hv

theorem getD_mem {k : ℕ} (hk : k < 216) : rels.getD k [] ∈ rels := by
  rw [List.getD_eq_getElem _ _ (by rw [rels_len]; exact hk)]
  exact List.getElem_mem _

theorem eq_of_inv {g h : ℕ} {W : Matrix (Fin 50) (Fin 50) (ZMod 7)} (hgh : X g * X h = 1)
    (hw : X h * W = 1) : W = X g := by
  rw [← Matrix.inv_eq_right_inv hw, Matrix.inv_eq_left_inv hgh]

theorem eq_of_rel {g : ℕ} (hg : g < 187) {v : List (ℕ × Bool)} (hv : (g, false) :: v ∈ rels) :
    (v.map Y).prod = X (g + 1) := by
  have h1 := rel_one hv
  rw [List.map_cons, List.prod_cons, Y_false] at h1
  exact eq_of_inv (hom.1 g hg) h1

theorem hXA : X 1 = CFSG.Sporadic.He.mA := by
  rw [CertificateChecks.KernelSpor.HeRels.mA_eq]
  change ordMat 7 50 12 600 (CFSG.KD.CJHeImg.RB 1) = ordMat 7 50 12 600 (CFSG.KD.OrdHe.RH 1)
  rw [Nat.eq_of_beq_eq_true rb1]

theorem hXB : X 2 = CFSG.Sporadic.He.mB := by
  rw [CertificateChecks.KernelSpor.HeRels.mB_eq]
  change ordMat 7 50 12 600 (CFSG.KD.CJHeImg.RB 2) = ordMat 7 50 12 600 (CFSG.KD.OrdHe.RH 2)
  rw [Nat.eq_of_beq_eq_true rb2]

theorem hXBi : X 189 = CFSG.Sporadic.He.mB⁻¹ := by
  rw [← hXB, Matrix.inv_eq_right_inv (hom.1 1 (by norm_num))]

theorem Y_seedLet {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 2) : Y (seedLet l) = heSeedMat l := by
  have : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · simp [seedLet, heSeedMat, Y_true, hXA]
  · simp [seedLet, heSeedMat, Y_true, hXA]
  · simp [seedLet, heSeedMat, Y_true, hXB]
  · simp [seedLet, heSeedMat, Y_false, hXBi]

theorem letters_of {w : List ℤ} (hw : lettersOK 2 w = true) : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  simp only [lettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hw
  exact hw

theorem prod_seedLet {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    ((w.map seedLet).map Y).prod = heWordMat w := by
  rw [heWordMat, List.map_map]
  congr 1
  exact List.map_congr_left fun l hl => Y_seedLet (hw l hl)

theorem heWordMat_flatten (l : List (List ℤ)) : heWordMat l.flatten = (l.map heWordMat).prod := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    rw [List.flatten_cons, List.map_cons, List.prod_cons, ← ih, heWordMat, heWordMat, heWordMat,
      List.map_append, List.prod_append]

theorem word_letters {i : ℕ} (hi : i < 8) : ∀ l ∈ hePiHeWords.getD i [], l ≠ 0 ∧ l.natAbs ≤ 2 := by
  have h := gw_letters
  have hm : hePiHeWords.getD i [] ∈ hePiHeWords := by
    rw [List.getD_eq_getElem _ _ (by rw [h.1]; omega)]
    exact List.getElem_mem _
  exact letters_of (h.2 _ hm)

theorem hXH {i t : ℕ} (hi : i < 8) (ht : t < 22) :
    heWordMat (chunk (hePiHeWords.getD i []) t) = X (12 + 22 * i + t) := by
  have hv := getD_mem (k := 22 * i + t) (by omega)
  rw [relsC i hi t ht] at hv
  have h := eq_of_rel (by omega) hv
  rw [prod_seedLet (w := chunk (hePiHeWords.getD i []) t) fun l hl => word_letters hi l
    (List.mem_of_mem_drop (List.mem_of_mem_take (by unfold chunk at hl; exact hl)))] at h
  rw [h]
  congr 1
  omega

theorem hXG {i : ℕ} (hi : i < 8) : heWordMat (hePiHeWords.getD i []) = X (3 + i) := by
  have hv := getD_mem (k := 176 + i) (by omega)
  rw [relsW i hi] at hv
  have h := eq_of_rel (by omega) hv
  rw [show 2 + i + 1 = 3 + i by omega] at h
  rw [← h, ← flat i hi, heWordMat_flatten, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [Function.comp_apply, Function.comp_apply, hXH hi (List.mem_range.1 ht), Y_true]
  congr 1
  omega

theorem Y_piLet (l : Fin 8 × Bool) : Y (piLet l) = hePiLetMat hePiHeWords l := by
  obtain ⟨⟨i, hi⟩, s⟩ := l
  have hG := hXG hi
  cases s
  · simp only [piLet, Y_false, hePiLetMat, Bool.false_eq_true, ↓reduceIte, hG]
    rw [show 3 + i = 2 + i + 1 by omega, Matrix.inv_eq_right_inv (hom.1 (2 + i) (by omega))]
  · simp only [piLet, Y_true, hePiLetMat, ↓reduceIte, hG, show 2 + i + 1 = 3 + i by omega]

theorem prod_piLet (w : List (Fin 8 × Bool)) :
    ((w.map piLet).map Y).prod = (w.map (hePiLetMat hePiHeWords)).prod := by
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => Y_piLet l

theorem mem_tail {v : List (ℕ × Bool)} (hv : v ∈ rels.drop 212) : v ∈ rels :=
  List.mem_of_mem_drop hv

theorem facts : HePiImageFacts := by
  unfold HePiImageFacts
  refine ⟨gw_letters.1, gw_letters.2, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hv : r.map piLet ∈ rels := by
      have : r.map piLet ∈ (rels.drop 184).take 28 := by
        rw [relsPi]
        exact List.mem_map_of_mem hr
      exact List.mem_of_mem_drop (List.mem_of_mem_take this)
    rw [← prod_piLet]
    exact rel_one hv
  · rw [← prod_piLet, eq_of_rel (g := 0) (by norm_num) (mem_tail (by rw [relsT]; simp)), hXA]
  · rw [← prod_piLet, eq_of_rel (g := 1) (by norm_num) (mem_tail (by rw [relsT]; simp)), hXB]
  · rw [← prod_piLet, eq_of_rel (g := 10) (by norm_num) (mem_tail (by rw [relsT]; simp))]
    have h := eq_of_rel (g := 10) (by norm_num) (mem_tail (by rw [relsT]; simp) :
      (10, false) :: heT1Letters.map seedLet ∈ rels)
    rw [prod_seedLet (letters_of (by decide))] at h
    exact h.symm

end CertificateChecks.KernelCosetJ.HeImg

end

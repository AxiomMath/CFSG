module

public import CFSG.Certificates.Kernel.Co2Smith.RowsSound
public import Certificates.Kernel.Co2Smith.LettersData
public import Certificates.Kernel.Sporadic.Co2.FRows
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.Co2Cert

theorem seedA_eq : co2RowsA = unpackR 22 (SM 0) := by
  rw [CertificateChecks.KernelSpor.Co2Faith.rowsA_eq]
  decide +kernel

theorem seedB_eq : co2RowsB = unpackR 22 (SM 1) := by
  rw [CertificateChecks.KernelSpor.Co2Faith.rowsB_eq]
  decide +kernel

theorem seeds_get : ∀ k < 2, seedRowsArr[k]! = unpackR 22 (SM k) := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact seedA_eq
  · exact seedB_eq

theorem sm_ok : (aWord.all (· < 2) && bWord.all (· < 2) &&
    Nat.beq (cK (wK SM aWord)) (cK (SM 2)) && Nat.beq (cK (wK SM bWord)) (cK (SM 3))) = true := by
  decide +kernel

theorem letters_get : ∀ k < 4, (letters seedRowsArr)[k]! = unpackR 22 (SM k) := by
  have h := sm_ok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, h2⟩, h3⟩ := h
  have hw : ∀ w : List Nat, (∀ k ∈ w, k < 2) →
      wRows seedRowsArr w = unpackR 22 (wK SM w) := fun w hw =>
    wRows_unpack _ _ w fun k hk => seeds_get k (hw k hk)
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact seedA_eq
  · exact seedB_eq
  · change wRows seedRowsArr aWord = _
    rw [hw aWord ha, eq_unpack_iff]
    exact Nat.eq_of_beq_eq_true h2
  · change wRows seedRowsArr bWord = _
    rw [hw bWord hb, eq_unpack_iff]
    exact Nat.eq_of_beq_eq_true h3

theorem gl_ok : (glLetterWords.size == 22 &&
    (List.range 22).all fun k => (glLetterWords[k]!).all (· < 4) &&
      Nat.beq (cK (wK SM glLetterWords[k]!)) (cK (LP k))) = true := by
  decide +kernel

theorem glRows_size : glRows.size = 22 := by
  have h := gl_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [glRows, h.1]

theorem glRows_get {k : Nat} (hk : k < 22) : glRows[k]! = unpackR 22 (LP k) := by
  have h := gl_ok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hs, h⟩ := h
  obtain ⟨hl, he⟩ := h k hk
  have e : glRows[k]! = mRows seedRowsArr glLetterWords[k]! := by
    unfold glRows
    rw [getElem!_pos _ k (by simp [hs, hk]), getElem!_pos glLetterWords k (by simp [hs, hk])]
    simp
  rw [e, mRows, wRows_unpack _ SM _ (fun j hj => letters_get j (hl j hj)), eq_unpack_iff]
  exact Nat.eq_of_beq_eq_true he

@[expose] noncomputable def glRowsK : Array (Array Nat) :=
  Array.ofFn (n := 22) fun k => unpackR 22 (LP k.val)

theorem glRows_eqK : glRows = glRowsK := by
  apply Array.ext
  · rw [glRows_size]
    simp [glRowsK]
  · intro i h1 h2
    have hi : i < 22 := by rwa [glRows_size] at h1
    rw [← getElem!_pos glRows i h1, glRows_get hi]
    simp [glRowsK]

theorem glR_eq {w : List Nat} (hw : ∀ k ∈ w, k < 22) : glR w = unpackR 22 (wK LP w) :=
  wRows_unpack _ _ w fun k hk => glRows_get (hw k hk)

theorem form_ok : ((List.range 3).all fun t => glForm t == unpackR 22 (FM t)) = true := by
  simp only [glForm, glU, glV, glW0, glW1, glW2, glW3, glConj, glX61, glD0h, glD1h, glZ, glR,
    glRows_eqK]
  decide +kernel

theorem glForm_eq {t : Nat} (ht : t < 3) : glForm t = unpackR 22 (FM t) := by
  have h := form_ok
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h t ht

end CertificateChecks.KernelCo2Smith

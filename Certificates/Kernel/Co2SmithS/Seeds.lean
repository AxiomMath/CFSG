module

public import Certificates.Kernel.Co2SmithS.LetsK
public import CFSG.Certificates.Kernel.Co2SmithS.RowsSound
public import CFSG.Sporadic.Co2Smith.CheckInputs
import Certificates.Kernel.Sporadic.Co2.FRows

public section

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co2SmithS CFSG.KC.Co2InvS CFSG.KC.Co1F2 CFSG.Sporadic.Co2Smith
  CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem seeds_eq : seedRowsArr = #[unpackR 22 (LT 0), unpackR 22 (LT 1)] := by
  unfold seedRowsArr
  rw [KernelSpor.Co2Faith.rowsA_eq, KernelSpor.Co2Faith.rowsB_eq]
  decide +kernel

theorem seeds_get : ∀ k < 2, seedRowsArr[k]! = unpackR 22 (LT k) := by
  intro k hk
  rw [seeds_eq]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl

theorem bounds : (∀ k ∈ aWord, k < 2) ∧ (∀ k ∈ bWord, k < 2) ∧
    ∀ j < 16, ∀ k ∈ sp6LetterMix j, k < 4 := by
  have h := lt_bounds
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem letters_get : ∀ k < 4, (letters seedRowsArr)[k]! = unpackR 22 (LT k) := by
  have hab := lt_ab
  simp only [Bool.and_eq_true] at hab
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact seeds_get 0 (by omega)
  · exact seeds_get 1 (by omega)
  · change wRows seedRowsArr aWord = _
    rw [wRows_eq seeds_get aWord bounds.1, Nat.eq_of_beq_eq_true hab.1]
  · change wRows seedRowsArr bWord = _
    rw [wRows_eq seeds_get bWord bounds.2.1, Nat.eq_of_beq_eq_true hab.2]

theorem mRows_eq {w : List Nat} (hw : ∀ k ∈ w, k < 4) :
    mRows seedRowsArr w = unpackR 22 (wK LT w) :=
  wRows_eq letters_get w hw

theorem sp6Letters_get : ∀ k < 16, (sp6LetterRows seedRowsArr)[k]! = unpackR 22 (LT (4 + k)) := by
  have h := lt_sp6
  simp only [List.all_eq_true, List.mem_range] at h
  intro k hk
  have e : (sp6LetterRows seedRowsArr)[k]! = mRows seedRowsArr (sp6LetterMix k) := by
    unfold sp6LetterRows
    rw [getElem!_pos _ k (by simpa using hk)]
    simp
  rw [e, mRows_eq (bounds.2.2 k hk), Nat.eq_of_beq_eq_true (h k hk)]

theorem mRows_two : mRows seedRowsArr [2] = unpackR 22 (mulV (LT 2) IDP) := by
  rw [mRows_eq (by simp)]
  rfl

theorem mRows_three : mRows seedRowsArr [3] = unpackR 22 (mulV (LT 3) IDP) := by
  rw [mRows_eq (by simp)]
  rfl

end CertificateChecks.KernelCo2SmithS

end

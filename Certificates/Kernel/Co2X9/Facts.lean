module

public import Certificates.Kernel.Co2X9.Checks
public import Certificates.Kernel.Co2X9.Bind
public import Certificates.Kernel.Co2Syl.Facts
public import CFSG.Certificates.Kernel.Co2X9.Sound
public import CFSG.RankThree.Co2.X9CertInputs

set_option exponentiation.threshold 600

public section

namespace CertificateChecks.KernelSpor.Co2X9

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2X9 CFSG.KC.TabMatGrp
  CFSG.RankThree.Co2 CertificateChecks.KernelSpor.Co2Syl

theorem XW_eq : XW = xWords9 := by decide +kernel
theorem DW_eq : DW = dWord := by decide +kernel
theorem FW_eq : FW = f9W := by decide +kernel
theorem EW_eq : EW = e1W := by decide +kernel

theorem xWords9_size : xWords9.size = 4 := by rw [← XW_eq]; exact XW_size
theorem xWords9_lt : ∀ j < 4, ∀ l ∈ xWords9[j]!, l < 42 := by rw [← XW_eq]; exact XW_lt
theorem dWord_lt : ∀ l ∈ dWord, l < 42 := by rw [← DW_eq]; exact DW_lt
theorem f9W_lt : ∀ l ∈ f9W, l < 42 := by rw [← FW_eq]; exact FW_lt
theorem e1W_lt : ∀ l ∈ e1W, l < 42 := by rw [← EW_eq]; exact EW_lt

theorem MatP_GX {j : ℕ} (hj : j < 4) : MatP 22 (GX j) = wordMat xWords9[j]! := by
  rw [Nat.eq_of_beq_eq_true (gens j hj), XW_eq, MatP_wordK (xWords9_lt j hj)]

theorem MatP_DX : MatP 22 DX = wordMat dWord := by
  rw [Nat.eq_of_beq_eq_true dX, DW_eq, MatP_wordK dWord_lt]

theorem MatP_FX : MatP 22 FX = wordMat f9W := by
  rw [Nat.eq_of_beq_eq_true fX, FW_eq, MatP_wordK f9W_lt]

theorem MatP_EX : MatP 22 EX = wordMat e1W := by
  rw [Nat.eq_of_beq_eq_true eX, EW_eq, MatP_wordK e1W_lt]

theorem genMonX : genMon GX = matGrp xWords9 := by
  refine genMon_eq_matGrp (fun j hj => ?_) fun k hk => ?_
  · rcases Nat.lt_or_ge j 4 with h | h
    · exact ⟨j, by rw [xWords9_size]; exact h, MatP_GX h⟩
    · obtain rfl : j = 4 := by omega
      exact ⟨3, by rw [xWords9_size]; omega, by
        rw [Nat.eq_of_beq_eq_true gensPad]; exact MatP_GX (by omega)⟩
  · rw [xWords9_size] at hk
    exact ⟨k, by omega, MatP_GX hk⟩

theorem treeX : TreeRecs EN.CF GX 6144 :=
  treeRecs_of (nb := 96) (by norm_num) blks (Nat.eq_of_beq_eq_true zero) (Nat.eq_of_beq_eq_true one)
    (by decide)

theorem comm9X : ∀ k < 4, wordMat xWords9[k]! * repMat 9 = repMat 9 * wordMat xWords9[k]! := by
  intro k hk
  rw [← MatP_GX hk, repMat_eq (j := 9) (by norm_num)]
  exact commK_sound (comm9 k (by omega))

theorem cardX : 6144 ≤ Nat.card (matGrp xWords9) := by
  rw [← genMonX]
  exact tree_card treeX

theorem neX : wordMat dWord ≠ 1 := by
  rw [← MatP_DX]
  exact neK_sound (blt_iff.1 ltD) neD

theorem commDX : ∀ k < 4, wordMat xWords9[k]! * wordMat dWord = wordMat dWord * wordMat xWords9[k]! := by
  intro k hk
  rw [← MatP_GX hk, ← MatP_DX]
  exact commK_sound (commD k (by omega))

theorem sqX : ∃ y ∈ matGrp xWords9, y * y = wordMat dWord := by
  rw [← genMonX, ← MatP_DX]
  exact sqW_sound treeX sqD

theorem cenX (hc : Nat.card (matGrp xWords9) ≤ 6144) :
    ∀ y ∈ matGrp xWords9, (∀ x ∈ matGrp xWords9, x * (y * y) = y * y * x) →
      y * y = 1 ∨ y * y = wordMat dWord := by
  rw [← genMonX] at hc
  rw [← genMonX, ← MatP_DX]
  exact cen_sound treeX hc fun k hk => (blkX_ok (nb := 96) (by norm_num) blks k hk).2

theorem conj9X : wordMat f9W * repMat 9 = repMat 9 * wordMat dWord * wordMat f9W := by
  have h := conjK_sound conj9
  rwa [MatP_mulV, MatP_FX, ← repMat_eq (j := 9) (by norm_num), MatP_DX] at h

theorem conj1X : wordMat e1W * repMat 1 = repMat 0 * wordMat dWord * wordMat e1W := by
  have h := conjK_sound conj1
  rwa [MatP_mulV, MatP_EX, ← repMat_eq (j := 1) (by norm_num),
    ← repMat_eq (j := 0) (by norm_num), MatP_DX] at h

theorem x9Facts :
    (∀ k < 4, wordMat xWords9[k]! * repMat 9 = repMat 9 * wordMat xWords9[k]!) ∧
    6144 ≤ Nat.card (matGrp xWords9) ∧
    wordMat dWord ≠ 1 ∧
    (∀ k < 4, wordMat xWords9[k]! * wordMat dWord = wordMat dWord * wordMat xWords9[k]!) ∧
    (∃ y ∈ matGrp xWords9, y * y = wordMat dWord) ∧
    (Nat.card (matGrp xWords9) ≤ 6144 → ∀ y ∈ matGrp xWords9,
      (∀ x ∈ matGrp xWords9, x * (y * y) = y * y * x) → y * y = 1 ∨ y * y = wordMat dWord) ∧
    (∀ l ∈ f9W, l < 42) ∧ wordMat f9W * repMat 9 = repMat 9 * wordMat dWord * wordMat f9W ∧
    (∀ l ∈ e1W, l < 42) ∧ wordMat e1W * repMat 1 = repMat 0 * wordMat dWord * wordMat e1W :=
  ⟨comm9X, cardX, neX, commDX, sqX, cenX, f9W_lt, conj9X, e1W_lt, conj1X⟩

end CertificateChecks.KernelSpor.Co2X9

end

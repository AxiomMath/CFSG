module

public import Certificates.Kernel.EvenSporG24.GenCheck

public section

open CFSG.EvenSporadicStandard.G24Model CFSG.Fischer CertificateChecks.EvenSporG24

namespace CertificateChecks.Batch27212

open CFSG.EvenSporadicStandard.G24Model CFSG.Fischer CertificateChecks.EvenSporG24

theorem f4_eq {x y : F4} (h : x.code.val = y.code.val) : x = y := by
  cases x
  cases y
  simp only [F4.mk.injEq]
  exact Fin.ext h

theorem genEntry_eq (j a b : Nat) :
    genEntry j a b = entL.getD (196 * j + 14 * a + b) 0 := by
  have hn : nLines = 1365 := rfl
  have hi : 2 * nLines + 196 * j + 14 * a + b = 2730 + (196 * j + 14 * a + b) := by
    rw [hn]
    omega
  rw [genEntry, hi, tbl_eq, entL, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem gEnt_code (j : Fin 16) (a b : Fin 14) :
    (gEnt j a b).code.val = genEntry j a b % 4 := rfl

theorem genOK_0 : genOK = true := by
  have h := genOKK_true
  simp only [genOKK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  unfold genOK
  refine decide_eq_true ⟨fun i c a b => ?_, fun i c a b => ?_⟩
  · have hx := (h i i.2 c.code c.code.2 a a.2 b b.2).1
    rw [xCodeN, dif_pos ⟨i.2, c.code.2, a.2, b.2⟩] at hx
    refine f4_eq (hx.trans ?_)
    rw [gEnt_code, genEntry_eq]
    rfl
  · have hy := (h i i.2 c.code c.code.2 a a.2 b b.2).2
    rw [yCodeN, dif_pos ⟨i.2, c.code.2, a.2, b.2⟩] at hy
    refine f4_eq (hy.trans ?_)
    rw [gEnt_code, genEntry_eq]
    rfl

end CertificateChecks.Batch27212

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.G24Model in
theorem certificate27212 : genOK = true := CertificateChecks.Batch27212.genOK_0

end Certificates

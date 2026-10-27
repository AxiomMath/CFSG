module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelPointsDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.LSubAlphaInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenModelInputs
import Certificates.Kernel.Misc.ON.Base
import Certificates.Kernel.Misc.ON.PointsFacts
import Certificates.Kernel.Misc.ON.Alpha
public import CFSG.Certificates.Kernel.Misc.F7FastSound

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON CFSG.KC.Misc.F7
open CFSG.RankThree.Native.ONTriple hiding ptMat
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

attribute [local irreducible] dotProduct

theorem fixXOK_spec {w n v : ℕ} (hw : w < nPt) (hn : n < 200) (hv : v < 200)
    (h : fixXOK w n v = true) :
    ptAct ((eM n)⁻¹ * eM v * eM n) (ptS w) = ptS w := by
  unfold fixXOK at h
  rw [(regOKK n hn).2, f7Img_eq (ptOK_parts hw).1, (regOKK v hv).2, imgS_enc, (regOKK n hn).1,
    imgS_enc, widenF_eq] at h
  obtain ⟨p, hpv, hp⟩ := echelon_ptMat hw
  set x : Mat45ˣ := (eM n)⁻¹ * eM v * eM n
  have e : ptMat w * (((eM n)⁻¹ : Mat45ˣ) : Mat45) * (((eM v)⁻¹ : Mat45ˣ) : Mat45) *
      ((eM n : Mat45ˣ) : Mat45) = ptMat w * ((x⁻¹ : Mat45ˣ) : Mat45) := by
    simp only [x, mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have hle : rowSpan (ptMat w * ((x⁻¹ : Mat45ˣ) : Mat45)) ≤ rowSpan (ptMat w) := by
    rw [← e]
    exact (inSpan8_iff hp.1 hpv).1 h
  have heq := rowSpan_mul_eq_of_le hp.1 hp.1 (Units.inv_mul x) hle
  rw [ptAct_apply, ptS_eq, ← rowSpan_mul, heq]

theorem alphaRows_eq : ∀ k < 9, ∀ l < 2, rowAt 1 k l = nthN (nthLN alphaRows k) l := by
  decide

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37 in
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven in
open CFSG.RankThree.Native.ONTriple in
theorem certificate291442 : ∀ k < 9, alphaPts.getD k 0 < 122760 ∧ ∀ l < 2, ∀ i < 2,
    ptAct ((eM ((rL.getD 1 []).getD l 0))⁻¹ * eM (vRegI 1 (rowAt 1 k l) i) *
      eM ((rL.getD 1 []).getD l 0)) (ptS (alphaPts.getD k 0)) = ptS (alphaPts.getD k 0) := by
  refine fun k hk => ?_
  have h := alphaB k hk
  unfold alphaOK at h
  rw [bAnd_eq, allN_iff, Nat.blt_eq] at h
  have hp : nthN alphaPts k < nPt := h.1
  refine ⟨by rw [← nthN_eq]; exact hp, fun l hl i hi => ?_⟩
  have h1 := (allN_iff 2 _).1 (h.2 l hl) i hi
  have hn : nthN (nthLN rL 1) l < 200 := by interval_cases l <;> decide
  have hv : vRegA (nthN (nthLN alphaRows k) l) i < 200 := by
    interval_cases k <;> interval_cases l <;> interval_cases i <;> decide
  have e1 : nthN (nthLN rL 1) l = (rL.getD 1 []).getD l 0 := by rw [nthN_eq, nthLN_eq]
  have e2 : vRegA (nthN (nthLN alphaRows k) l) i = vRegI 1 (rowAt 1 k l) i := by
    rw [vRegA, nthN_eq, nthLN_eq, alphaRows_eq k hk l hl]
  have := fixXOK_spec hp hn hv h1
  rw [e1, e2, nthN_eq alphaPts k] at this
  exact this

end Certificates

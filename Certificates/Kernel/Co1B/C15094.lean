module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeTwoCInputs
public import Certificates.Kernel.Co1B.Chk15094
public import Certificates.Kernel.Co1B.C2047
public import Certificates.Kernel.Co1B.C2041

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C15094

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.KC.Co1F2 CFSG.KC.Co1B
open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1.InvNative
open CertificateChecks.KernelCo1B.C2047
open CFSG.ComponentClassification.RankTwoExceptional.HoltFree

theorem unpack_oneK : unpack 24 24 oneK = one () := by
  rw [← unpackR_eq_unpack, CertificateChecks.KernelCo1B.one_eq]

theorem mulU (X Y : Nat) : mul (unpack 24 24 X) (unpack 24 24 Y) = unpack 24 24 (mulWK X Y) :=
  CFSG.KS.SporSch.M24.mul_unpackW X Y

theorem pow_eq (M : Nat) : ∀ e, pow (unpack 24 24 M) e = unpack 24 24 (powWK M e)
  | 0 => by
    change one () = unpack 24 24 oneK
    rw [unpack_oneK]
  | e + 1 => by
    rw [pow, pow_eq M e, mulU]
    change _ = unpack 24 24 (CFSG.KC.Loop.strictN (powWK M e) fun a => mulWK a M)
    rw [CFSG.KC.F2W.strictN_eq]

theorem dagRows_eq : twoCDagRows = SL := by
  unfold twoCDagRows
  rw [dag₂_eq]
  rfl

theorem p_eq : holtFreePRows = unpack 24 24 PP := by
  unfold holtFreePRows PP
  rw [dagRows_eq, SL_get (by decide), SL_get (by decide), mulU]

theorem q_get {l : Nat} (hl : l < 11) : twoCQRows.getD l (one ()) = unpack 24 24 (QM l) := by
  rw [← qRows_get hl, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [qRows_len]; exact hl), Option.getD_some, Option.getD_some]

theorem w_eq (Q : Nat) : holtFreeWRows (unpack 24 24 Q) = unpack 24 24 (WK Q) := by
  unfold holtFreeWRows WK
  rw [p_eq, pow_eq, mulU, mulU, mulU]

theorem a_eq : holtFreeA = unpack 24 24 AK := by
  unfold holtFreeA AK
  rw [q_get (by decide), w_eq]

theorem b_eq : holtFreeB = unpack 24 24 BK := by
  unfold holtFreeB BK
  rw [q_get (by decide), w_eq]

theorem f_eq : holtFreeF = unpack 24 24 FK := by
  unfold holtFreeF FK
  rw [q_get (by decide), w_eq]

theorem fixU (M : Nat) : xFixCount certVecs (unpack 24 24 M) = fixTabK (trK 24 M) CV.F 117 := by
  rw [← unpackR_eq_unpack]
  exact CertificateChecks.KernelCo1B.xFix_eq rfl

theorem order_check : holtFreeOrderCheck = true := by
  have h := xO
  rw [Bool.and_eq_true, unpack_oneK] at h
  have h11 : pow holtFreePRows 11 = one () := by
    rw [p_eq, pow_eq, Nat.eq_of_beq_eq_true h.1, unpack_oneK]
  have hv : validRows holtFreePRows = true := by
    rw [p_eq, ← unpackR_eq_unpack]
    exact validRows_unpackR _
  unfold holtFreeOrderCheck
  rw [h11, hv, beq_self_eq_true, Bool.true_and, Bool.and_true, p_eq]
  exact h.2

theorem fix_check : holtFreeFixCheck = true := by
  unfold holtFreeFixCheck
  rw [gt_eq, Array.all_eq_true]
  intro i hi
  have hi' : i < 2048 := by simpa [bfsTree, hN.2.1] using hi
  have h := MatL.allN_iff.1 xFix i hi'
  simp only [bfsTree, Array.getElem_ofFn]
  rw [p_eq, mulU, mulU, iotaC_u, ← MatL.unpack_idM]
  exact h

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native in
open CFSG.ComponentClassification.RankTwoExceptional.HoltFree in
theorem c15094 : holtFreeOrderCheck = true
    ∧ holtFreeFixCheck = true
    ∧ xFixCount certVecs holtFreeA = 2280
    ∧ xFixCount certVecs holtFreeB = 264
    ∧ xFixCount certVecs (mul holtFreeB iotaCRows) = 264
    ∧ xFixCount certVecs holtFreeF = 2280
    ∧ xFixCount certVecs (mul holtFreeA holtFreeF) = 2280 := by
  refine ⟨order_check, fix_check, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_eq, fixU, Nat.eq_of_beq_eq_true xA]
  · rw [b_eq, fixU, Nat.eq_of_beq_eq_true xB]
  · rw [b_eq, iotaC_u, mulU, fixU, Nat.eq_of_beq_eq_true xBC]
  · rw [f_eq, fixU, Nat.eq_of_beq_eq_true xF]
  · rw [a_eq, f_eq, mulU, fixU, Nat.eq_of_beq_eq_true xAF]

end CertificateChecks.KernelCo1B.C15094

end

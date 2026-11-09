module

public import Certificates.Kernel.Co1B.Chk2047
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BFix
public import Certificates.Data.Co1HoltFreeTwoC
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Co1BFixPSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C15094

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.KC.Co1F2 CFSG.KC.Co1B
open CertificateChecks.KernelCo1B.C2047
open CFSG.ComponentClassification.RankTwoExceptional.HoltFree

@[expose] noncomputable def PP : Nat := mulWK (D2.M Data.pIdx.1) (D2.M Data.pIdx.2)

@[expose] noncomputable def WK (q : Nat) : Nat := mulWK q (mulWK (mulWK PP q) (powWK PP 10))

@[expose] noncomputable def AK : Nat := WK (QM Data.aIdx)

@[expose] noncomputable def BK : Nat := WK (QM Data.bIdx)

@[expose] noncomputable def FK : Nat := WK (QM Data.fIdx)

theorem xO : (Nat.beq (powWK PP 11) oneK && (unpack 24 24 PP != unpack 24 24 oneK)) = true := by
  quickRfl

theorem pg_eq_mod (w P i : Nat) : pg w (CFSG.KS.mask w) P i = P / 2 ^ (w * i) % 2 ^ w := by
  change Nat.land (Nat.shiftRight P (w * i)) (Nat.sub (1 <<< w) 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  change (P >>> (w * i)) &&& (2 ^ w - 1) = _
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem unpack_beq_mod (n w A B : Nat) :
    (unpack n w A == unpack n w B) = Nat.beq (A % 2 ^ (n * w)) (B % 2 ^ (n * w)) := by
  have key : unpack n w A = unpack n w B ↔ A % 2 ^ (n * w) = B % 2 ^ (n * w) := by
    rw [unpack, unpack, ← Array.toList_inj, Array.toList_ofFn, Array.toList_ofFn, List.ofFn_inj]
    simp only [funext_iff, pg_eq_mod]
    constructor
    · intro h
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [Nat.testBit_mod_two_pow]
      by_cases hj : j < n * w
      · have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
        have hi : j / w < n := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hj)
        have := congrArg (fun x => x.testBit (j % w)) (h ⟨j / w, hi⟩)
        simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.mod_lt j hw,
          decide_true, Bool.true_and, Nat.mod_add_div] at this
        simp [hj, this]
      · simp [hj]
    · intro h i
      apply Nat.eq_of_testBit_eq
      intro r
      simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      by_cases hr : r < w
      · have hlt : r + w * i.val < n * w := by
          have : w * (i.val + 1) ≤ w * n := Nat.mul_le_mul_left w i.isLt
          rw [Nat.mul_succ] at this
          rw [Nat.mul_comm n w]
          omega
        have := congrArg (fun x => x.testBit (r + w * i.val)) h
        simp only [Nat.testBit_mod_two_pow, hlt, decide_true, Bool.true_and] at this
        simp [hr, this]
      · simp [hr]
  rw [Bool.eq_iff_iff, beq_iff_eq, key, Nat.beq_eq]

theorem xFix : allN 2048 (fun i => !(unpack 24 24 (mulWK PP (QT.P i)) ==
    unpack 24 24 (mulWK (QT.P i) PP)) || unpack 24 24 (QT.P i) == unpack 24 24 idM ||
    unpack 24 24 (QT.P i) == unpack 24 24 IC) = true := by
  simp only [unpack_beq_mod]
  quickRfl

theorem xA : Nat.beq (fixTabK (trK 24 AK) CV.F 117) 2280 = true := by
  rw [← fixTabP_eq]
  quickRfl
theorem xB : Nat.beq (fixTabK (trK 24 BK) CV.F 117) 264 = true := by
  rw [← fixTabP_eq]
  quickRfl
theorem xBC : Nat.beq (fixTabK (trK 24 (mulWK BK IC)) CV.F 117) 264 = true := by
  rw [← fixTabP_eq]
  quickRfl
theorem xF : Nat.beq (fixTabK (trK 24 FK) CV.F 117) 2280 = true := by
  rw [← fixTabP_eq]
  quickRfl
theorem xAF : Nat.beq (fixTabK (trK 24 (mulWK AK FK)) CV.F 117) 2280 = true := by
  rw [← fixTabP_eq]
  quickRfl

end CertificateChecks.KernelCo1B.C15094

end

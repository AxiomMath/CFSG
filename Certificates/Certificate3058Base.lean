
module

public import CFSG.Certificates.Kernel.Trace6091.TwinEq
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Certificate3015
public import Certificates.Data.BT2K1Vocab

@[expose] public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.KC.KDense CFSG.KC.Trace6091

namespace CertificateChecks.Batch3058

theorem kTheta0 : ∀ q < 512, pairT 3 (thetaT (2 * q)) = pairT 3 (thetaT (2 * q ^^^ 60)) := by
  decide +kernel

theorem kTheta1 : ∀ q < 512,
    pairT 3 (thetaT (2 * (q + 512))) = pairT 3 (thetaT (2 * (q + 512) ^^^ 60)) := by
  decide +kernel

theorem kTheta2 : ∀ q < 512,
    pairT 3 (thetaT (2 * (q + 1024))) = pairT 3 (thetaT (2 * (q + 1024) ^^^ 60)) := by
  decide +kernel

theorem kTheta3 : ∀ q < 512,
    pairT 3 (thetaT (2 * (q + 1536))) = pairT 3 (thetaT (2 * (q + 1536) ^^^ 60)) := by
  decide +kernel

theorem kTheta : ∀ q < 2048, pairT 3 (thetaT (2 * q)) = pairT 3 (thetaT (2 * q ^^^ 60)) := by
  intro q hq
  rcases (by omega : q < 512 ∨ (512 ≤ q ∧ q < 1024) ∨ (1024 ≤ q ∧ q < 1536) ∨ 1536 ≤ q) with
    h | h | h | h
  · exact kTheta0 q h
  · have := kTheta1 (q - 512) (by omega)
    rwa [Nat.sub_add_cancel h.1] at this
  · have := kTheta2 (q - 1024) (by omega)
    rwa [Nat.sub_add_cancel h.1] at this
  · have := kTheta3 (q - 1536) (by omega)
    rwa [Nat.sub_add_cancel h] at this

theorem tb_xor (a b : ℕ) : (a ^^^ b).testBit 0 = (a.testBit 0 ^^ b.testBit 0) :=
  Nat.testBit_xor a b 0

theorem pi0_bit (a : ℕ) : (Model.pi0N a).testBit 0 = false := by
  unfold Model.pi0N
  cases h : a.testBit 0
  · rw [ite_eq_right (by simp), Nat.xor_zero, h]
  · rw [ite_eq_left rfl, tb_xor, h]
    decide

theorem pi0_of {a : ℕ} (h : a.testBit 0 = false) : Model.pi0N a = a := by
  unfold Model.pi0N
  rw [ite_eq_right (by simp [h]), Nat.xor_zero]

theorem pi0_odd {a : ℕ} (h : a.testBit 0 = true) : Model.pi0N a = a ^^^ 63 := by
  unfold Model.pi0N
  rw [ite_eq_left h]

theorem theta_eq {p : ℕ} (hp : p < 4096) (h0 : p.testBit 0 = false) :
    Model.thetaBit p 3 = Model.thetaBit (p ^^^ 60) 3 := by
  have e : 2 * (p / 2) = p := by
    have := Nat.mod_two_eq_zero_iff_testBit_zero.2 h0
    omega
  have k := kTheta (p / 2) (by omega)
  rw [e, thetaT_eq, thetaT_eq, pairT_eq, pairT_eq] at k
  unfold Model.thetaBit
  revert k
  cases Model.pairN 3 (Model.thetaN p) <;> cases Model.pairN 3 (Model.thetaN (p ^^^ 60)) <;>
    simp

theorem bit_3 {p : ℕ} (h0 : p.testBit 0 = false) : (p ^^^ 3).testBit 0 = true := by
  rw [tb_xor, h0]
  decide

theorem bit_60 {p : ℕ} (h0 : p.testBit 0 = false) : (p ^^^ 60).testBit 0 = false := by
  rw [tb_xor, h0]
  decide

theorem shift_eq {p : ℕ} (h0 : p.testBit 0 = false) : Model.shiftN 3 p = p ^^^ 60 := by
  unfold Model.shiftN
  rw [pi0_odd (bit_3 h0), Nat.xor_assoc]
  rfl

theorem shift_back {p : ℕ} (h0 : p.testBit 0 = false) : Model.shiftN 3 (p ^^^ 60) = p := by
  unfold Model.shiftN
  rw [pi0_odd (bit_3 (bit_60 h0)), Nat.xor_assoc, Nat.xor_assoc]
  change p ^^^ 0 = p
  rw [Nat.xor_zero]

end CertificateChecks.Batch3058

namespace Certificates

end Certificates

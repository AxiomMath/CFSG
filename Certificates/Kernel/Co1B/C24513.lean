module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneFourthInputs
public import Certificates.Kernel.Co1B.Syl2B
public import Certificates.Kernel.Co1B.KF24513

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Block.Native CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.InvNative
  CFSG.EvenSporadicStandard.TwoCo1.HypOne CertificateChecks.KernelSporSch.Co1Packed

theorem aR_D1 : aR = unpack 24 24 (Cent2045.D1.M 0) := by
  rw [aR_u, Nat.eq_of_beq_eq_true Cent2045.kb0]

theorem validRows_aR : validRows aR = true := by
  rw [aR_u, ← unpackR_eq_unpack]
  exact CFSG.KC.Co1F2.validRows_unpackR _

theorem fourth_ok : (bfsTree ST.N ST.P ST.PAR ST.LAB).pts.all
    (fun p => mul (mul p p) (mul p p) != aR) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 32768 := by simpa [bfsTree, hN.1] using hi
  have hs : ∀ y (k : Nat → Bool), CFSG.KC.Enum.strictB y k = k y := fun y k => by
    cases y <;> rfl
  have h := MatL.allN_iff.1 kF i hi'
  rw [hs] at h
  simp only [bfsTree, Array.getElem_ofFn]
  rw [mul_unpackW, mul_unpackW, aR_D1]
  exact h

open Certificates in
theorem c24513 : CFSG.EvenSporadicStandard.TwoCo1.HypOne.fourthRootCheckB = true := by
  unfold fourthRootCheckB fourthRootCheckOf
  simp only []
  rw [dagS_eq, bray_eq, dag₁_eq, sg_eq, gt_eq.1, gt_eq.2, bray_ok, validRows_aR, fourth_ok]
  simp [bfsTree, hN.1]

end CertificateChecks.KernelCo1B.Syl2B

end

module

public import CFSG.LargeExtraspecial.S14SMKTransCheck
public import Certificates.Data.Kernel.SmithL6K
import Certificates.Kernel.SmithEK.GlueNL
public import Std.Data.HashMap

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithE CFSG.Sporadic.Th

open CFSG.SmithE CFSG.Fischer.Native CFSG.Sporadic.Th.Native in
theorem certificate21275 :
    (collInvs collS2 (collMeet collS2)).size = 675 ∧
    (∀ v < 675, (collInvs collS2 (collMeet collS2))[v]!.size = 21 ∧
      ∀ k < 21, ((collInvs collS2 (collMeet collS2))[v]!)[k]! < 21) ∧
    (∀ j < 5,
      (∀ x < 693, (liftTab tvTabs j)[x]! < 693 ∧ (CFSG.SmithE.invTab (liftTab tvTabs j))[x]! < 693 ∧
        (CFSG.SmithE.invTab (liftTab tvTabs j))[(liftTab tvTabs j)[x]!]! = x ∧
        (liftTab tvTabs j)[(CFSG.SmithE.invTab (liftTab tvTabs j))[x]!]! = x) ∧
      (∀ p < 693, ∀ x < 693, (liftTab tvTabs j)[CFSG.Sporadic.Th.Native.ap tvTabs[p]! x]! =
        CFSG.Sporadic.Th.Native.ap tvTabs[(liftTab tvTabs j)[p]!]! (liftTab tvTabs j)[x]!) ∧
      ∀ k < 21, ((uaFlags uaPts)[0]!)[(liftTab tvTabs j)[(uaPts[0]!)[k]!]!]! = true) ∧
    CFSG.SmithL6.K.Reach 675 34
      (fun v => ((List.range 4).map fun j => sArrT uaPts[0]! (liftTab tvTabs (j + 1))).any
        fun r => r == (collInvs collS2 (collMeet collS2))[v]!)
      (fun g u v => collComp (collComp (stabWords.map (stabSig tvTabs uaPts[0]!))[g]!
          (collInvs collS2 (collMeet collS2))[u]!)
        (stabWords.map fun w => stabSig tvTabs uaPts[0]! (w.2, w.1))[g]! ==
          (collInvs collS2 (collMeet collS2))[v]!) := by
  have hI := KernelSmithEK.collI_facts
  have hR := KernelSmithEK.reachL
  unfold CFSG.LargeExtraspecial.SMod20.collI at hI hR
  refine ⟨hI.1, hI.2, fun j hj => ?_, hR⟩
  obtain ⟨ha, hb, hc⟩ := KernelSmithEK.liftFacts j hj
  refine ⟨fun x hx => ?_, fun p hp x hx => ?_, hc⟩
  · have := (allIn_eq_true.1 ha) x (Nat.zero_le _) hx
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · exact beq_iff_eq.1 ((allIn_eq_true.1 ((allIn_eq_true.1 hb) p (Nat.zero_le _) hp)) x
      (Nat.zero_le _) hx)

end Certificates

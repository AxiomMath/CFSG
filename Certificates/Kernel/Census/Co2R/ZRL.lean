module

public import Certificates.Kernel.Census.Co2R.DataL
import all Certificates.Kernel.Census.Co2R.DataL
import all Certificates.Kernel.Census.Co2R.Data
import all Certificates.Data.Kernel.Census.PackedConjL
import all Certificates.Data.Kernel.Census.PackedL
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Co2R.Z

open CFSG.KC.Census CertificateChecks.KernelCensus.Co2R

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[expose] noncomputable def lenR (l : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun _ _ ih a => CFSG.KC.Enum.strictN (Nat.succ a) ih) l a

theorem lenR_eq : ∀ (l : List Nat) (a : Nat), lenR l a = a + l.length
  | [], a => by simp [lenR]
  | x :: l, a => by
    change CFSG.KC.Enum.strictN (Nat.succ a) (fun a => lenR l a) = a + (x :: l).length
    have hs : ∀ (y : Nat) (k : Nat → Nat), CFSG.KC.Enum.strictN y k = k y := by
      intro y k; cases y <;> rfl
    rw [hs, lenR_eq l, List.length_cons]
    omega

theorem kIH : invHead 32 r = true := by
  have e : r.d.wt.length = lenR r.d.wt 0 := by rw [lenR_eq, Nat.zero_add]
  unfold invHead
  rw [e]
  quickRfl

theorem kZl : Nat.ble (r.d.us.toList.zip r.d.roots).length (4 * 1536) = true := by quickRfl

theorem kFitC : fitW 160 r.d.cs.toList = true := by quickRfl

theorem kFitI : fitW 160 r.d.ci.toList = true := by quickRfl

theorem kRL0 : rootChunkL 32 160 r 1536 0 = true := by quickRfl
theorem kRL1 : rootChunkL 32 160 r 1536 1 = true := by quickRfl
theorem kRL2 : rootChunkL 32 160 r 1536 2 = true := by quickRfl
theorem kRL3 : rootChunkL 32 160 r 1536 3 = true := by quickRfl

end CertificateChecks.KernelCensus.Co2R.Z

end

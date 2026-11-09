module

public import Certificates.Kernel.Co2Smith.WDefs
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import CFSG.Sporadic.Co2Smith.GlNJData

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native CFSG.KS.Co2M
open CertificateChecks.KernelSporSch.Co2M

@[expose] noncomputable def fixVK (A : Nat) : Nat :=
  let T := CFSG.KC.Co1F2.trK 22 A
  ((List.range 2300).filter fun i =>
    Nat.beq (CFSG.KC.M1F2.vmF 22 T (VG (PV 0) i)) (VG (PV 0) i)).length

@[expose] noncomputable def njFixK (lo n : Nat) : Bool :=
  (List.range n).all fun j => (lo + j) == 0 || glNJOm.contains (lo + j) ||
    fixVK (jcK (lo + j)) != 284

theorem njFixK_add (lo a b : Nat) : njFixK lo (a + b) = (njFixK lo a && njFixK (lo + a) b) := by
  unfold njFixK
  rw [List.range_add, List.all_append, List.all_map]
  simp only [Function.comp_def, Nat.add_assoc]

theorem njFixK_chunks (lo m : Nat) : ∀ k : Nat, (∀ c < k, njFixK (lo + c * m) m = true) →
    njFixK lo (k * m) = true
  | 0, _ => by simp [njFixK]
  | k + 1, h => by
    rw [Nat.add_mul, Nat.one_mul, njFixK_add, njFixK_chunks lo m k (fun c hc => h c (by omega)),
      h k (by omega)]
    all_goals rfl

theorem njFixK_of_chunks (lo k m n : Nat) (hn : k * m = n)
    (h : ∀ c < k, njFixK (lo + c * m) m = true) : njFixK lo n = true := by
  subst hn
  exact njFixK_chunks lo m k h

end CertificateChecks.KernelCo2Smith

module

public import CFSG.Sporadic.Co2Jc.Words
public import CFSG.Certificates.Kernel.Enum.Defs
public meta import CFSG.Sporadic.Co2Jc.Words
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Jc

meta def njArrs : Array (Array Nat) :=
  #[0, 1, 2].map fun k => Array.ofFn (n := 1024) fun x => CFSG.Sporadic.Co2Smith.Native.glNJT k x.val

end CertificateChecks.KernelCo2Jc

#kmisc_packarrs CertificateChecks.KernelCo2Jc.NJ CertificateChecks.KernelCo2Jc.njArrs 10

namespace CertificateChecks.KernelCo2Jc

open CFSG.KC.Enum

set_option maxRecDepth 400000

@[expose] noncomputable def njK (k x : Nat) : Nat :=
  if k < 3 ∧ x < 1024 then pg 10 1023 (NJ k) x else CFSG.Sporadic.Co2Smith.Native.glNJT k x

theorem nj_ok : ((List.range 3).all fun k => (List.range 1024).all fun x =>
    CFSG.Sporadic.Co2Smith.Native.glNJT k x == pg 10 1023 (NJ k) x) = true := by
  decide +kernel

theorem glNJT_eq_njK (k x : Nat) : CFSG.Sporadic.Co2Smith.Native.glNJT k x = njK k x := by
  unfold njK
  split_ifs with h
  · have hk := List.all_eq_true.1 nj_ok k (List.mem_range.2 h.1)
    exact beq_iff_eq.1 (List.all_eq_true.1 hk x (List.mem_range.2 h.2))
  · rfl

theorem wordAct_eq (w : List Nat) (m : Nat) :
    CFSG.Sporadic.Co2Jc.wordAct w m = w.foldr (fun k acc => njK k acc) m := by
  unfold CFSG.Sporadic.Co2Jc.wordAct
  simp only [glNJT_eq_njK]

end CertificateChecks.KernelCo2Jc

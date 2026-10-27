module

public import Certificates.Data.Kernel.B433Alt.Struct
public import Certificates.Kernel.B433Alt.Data.St

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433.Neg

open CFSG.KC.B4A

@[expose] noncomputable def upd (F : Nat → Nat) (k v : Nat) (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (F r) v (Nat.beq r k)

open CFSG.KD.B4A in
theorem neg_inv : foldOK LP RD (upd RW 3002 (RW 3001)) PW RJ SS 3002 = false := by
  decide +kernel

open CFSG.KD.B4A in
theorem neg_trans_pt : foldOK LP (upd RD 3001 (RD 3001 + 2 ^ 20)) RW PW RJ SS 3001 = false := by
  decide +kernel

open CFSG.KD.B4A in
theorem neg_walk : foldOK LP RD RW PW (upd RJ 3000 (RJ 3000 / 2)) SS 3000 = false := by
  decide +kernel

open CFSG.KD.B4A in
theorem neg_seed_state : foldOK LP RD RW PW RJ (upd SS 3141 (SS 3141 + 1)) 3140 = false := by
  decide +kernel

open CFSG.KD.B4A in
theorem neg_diff : foldOK LP RD RW PW (upd RJ 3167 (RJ 3167 + 2 ^ 20)) SS 3167 = false := by
  decide +kernel

open CFSG.KD.B4A in
theorem neg_pair : foldOK (upd LP 15 (LP 16)) RD RW PW RJ SS 3001 = false := by
  decide +kernel

end CertificateChecks.KernelB433.Neg

end

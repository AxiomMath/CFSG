module

public import Certificates.Kernel.Census.Pg.Chain

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPg

open CFSG.KC.Enum CFSG.KS CFSG.KC.W16Pg

@[expose] noncomputable def swapS (j : Nat) : Nat :=
  if j = 0 then
    C.S 0 ^^^ (((pg 8 (mask 8) (C.S 0) 1 ^^^ pg 8 (mask 8) (C.S 0) 2) <<< 8) |||
      ((pg 8 (mask 8) (C.S 0) 1 ^^^ pg 8 (mask 8) (C.S 0) 2) <<< 16))
  else C.S j

@[expose] noncomputable def badMul (a b : Nat) : Nat := if a = 0 ∧ b = 5 then 6 else mulCK ET a b

theorem aut_neg : autK ET swapS = false := by decide +kernel

theorem table_neg : tableG badMul = false := by decide +kernel

theorem cand_neg : candG (fun a b => if a = 32 ∧ b = 32 then 5 else mulCK ET a b) = false := by
  decide +kernel

end CertificateChecks.KernelPg

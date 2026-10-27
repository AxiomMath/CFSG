module

public import CFSG.Certificates.Kernel.BabyMonster.PktTab
public import Certificates.Kernel.BabyMonster.PktBind
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
public import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Algebra.Order.Ring.Int

public section

namespace CertificateChecks.KernelBM.A0

open CFSG.KC.BM CFSG.KC.BM.Pkt CFSG.KC.BM.Dyadic

set_option maxRecDepth 100000

@[expose] noncomputable def pkT (k : Nat) : Nat :=
  tableOf (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S k)

theorem mono2 : monoOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S 2) (pkT 2) = true := by quickRfl
theorem mono4 : monoOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S 4) (pkT 4) = true := by quickRfl
theorem mono5 : monoOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S 5) (pkT 5) = true := by quickRfl
theorem mono10 : monoOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S 10) (pkT 10) = true := by
  quickRfl
theorem mono17 : monoOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S 17) (pkT 17) = true := by
  quickRfl

theorem tab2 : tabOK (pkT 2) = true := by quickRfl
theorem tab4 : tabOK (pkT 4) = true := by quickRfl
theorem tab5 : tabOK (pkT 5) = true := by quickRfl
theorem tab10 : tabOK (pkT 10) = true := by quickRfl
theorem tab17 : tabOK (pkT 17) = true := by quickRfl
theorem tabG6 : tabOK (nthN G6.b0 0) = true := by quickRfl
theorem tabG0 : tabOK (nthN G0.b0 0) = true := by quickRfl

@[expose] noncomputable def c1 : Nat := compT (nthN G6.b0 0) (nthN G0.b0 0)
@[expose] noncomputable def c2 : Nat := compT c1 (pkT 2)
@[expose] noncomputable def c3 : Nat := compT c2 (pkT 4)
@[expose] noncomputable def c4 : Nat := compT c3 (pkT 5)
@[expose] noncomputable def c5 : Nat := compT c4 (pkT 10)

theorem tab_c1 : tabOK c1 = true := by quickRfl
theorem tab_c2 : tabOK c2 = true := by quickRfl
theorem tab_c3 : tabOK c3 = true := by quickRfl
theorem tab_c4 : tabOK c4 = true := by quickRfl
theorem tab_c5 : tabOK c5 = true := by quickRfl

theorem prod_a0 : Nat.beq (compT c5 (pkT 17)) (nthN G26.b0 0) = true := by quickRfl

end CertificateChecks.KernelBM.A0

end

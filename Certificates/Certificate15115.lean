module

public import CFSG.Sporadic.Bridge.VecSurj
public import Certificates.Data.CFSGNative.Ru.Data
public import Certificates.Data.GMS78RuNECheck
import Certificates.Kernel.GMS78.W115
import Certificates.Kernel.GMS78.WNE
import Certificates.Kernel.GMS78.Coset.Cards115
public import CFSG.Sporadic.Th.F2Spec
import CFSG.Certificates.CosetTableShort

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GMS78 CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj
  CFSG.ComponentClassification.GMS78.RuPi7 CFSG.ComponentClassification.GMS78.RuAsm in
theorem certificate15115 : (Finite (CFSG.CosetTable.PG 7 RuNE.pi7bRels) ∧
      Nat.card (CFSG.CosetTable.PG 7 RuNE.pi7bRels) ≤ 145926144000) ∧
    (∀ r ∈ RuNE.pi7bRels, wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
      (r.map fun l => (l.1.val, l.2)) = 1) ∧
    (Finite (CFSG.CosetTable.PG RuNE.sub1.length RuNE.relsM1) ∧
      Nat.card (CFSG.CosetTable.PG RuNE.sub1.length RuNE.relsM1) ≤ 245760) ∧
    (∀ p ∈ RuNE.neBasisEqs,
      wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) (ruAsmNatWord p.1) =
        wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) (ruAsmNatWord p.2)) ∧
    (∀ i < 64, i ≠ 0 → wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
      (ruAsmNatWord (RuNE.neTWord i)) ≠ 1) ∧
    (∀ t ∈ RuNE.neOrbitWit, ∃ j : ℕ,
      wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
          (ruAsmNatWord (RuNE.neOrbitX t ++ ruE0Words.getD j [])) ≠
        wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
          (ruAsmNatWord (ruE0Words.getD j [] ++ RuNE.neOrbitX t))) ∧
    (∀ k < 6, ∀ i < 64, (RuNE.neConjTab.getD k []).getD i 0 = RuNE.neConjLin k i) ∧
    RuNE.neActCheck = true ∧ RuNE.neW0Check = true :=
  ⟨KernelGMS78.Coset.card_pi7b, KernelGMS78.W.pi7bRels_hold, KernelGMS78.Coset.card_M1,
    KernelGMS78.W.neBasisEqs_hold, KernelGMS78.W.neT_ne_one, KernelGMS78.W.neOrbitX_comm_ne,
    KernelGMS78.W.neConjTab_lin, KernelGMS78.NE.neActCheck_true, KernelGMS78.NE.neW0Check_true⟩

end Certificates

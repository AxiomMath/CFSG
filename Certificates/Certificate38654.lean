module

public import Certificates.Data.SmithL6IdCheck
public import CFSG.GF2Type.SmithTypeE.LMod.Basic
import Certificates.Kernel.SmithL6K.GlueQ

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod in
open CFSG.LargeExtraspecial.SMod20 (V) in
theorem certificate38654 : idChkWt = true ∧ idChkWtInj = true ∧
    ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
      (∀ s, ∃ p : Fin 1953, p ∈ planeSet 0 ∧ ∃ k : Fin 1395, ¬ Opp 0 k ∧
        v s = tvLin p.val (wtV k) + wtV k) ∧
      ∀ j : Fin 1395, wtV j ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW 0 j = true :=
  ⟨KernelSmithL6K.idChkWt_holds, KernelSmithL6K.idChkWtInj_holds, KernelSmithL6K.qa_zero⟩

end Certificates

module

public import Certificates.Kernel.SmithEK.GlueQ

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithE CFSG.LargeExtraspecial.SMod20 in
theorem certificate21267 :
    (∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
      (∀ s, ∃ p : Fin 693, p ∈ planeSet 0 ∧ ∃ k : Fin 891, ¬ Opp 0 k ∧
        v s = tvLin p.val (wtV k.val) + wtV k.val) ∧
      ∀ j : Fin 891, wtV j.val ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW 0 j.val = true) ∧
    ∀ v : V, (∀ p ∈ planeSet 0, tvLin p.val v = v) ↔ v = 0 ∨ v = wtV 0 :=
  ⟨KernelSmithEK.qa0, KernelSmithEK.cv0⟩

end Certificates

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.SylowSound
import Certificates.Kernel.EvenSporSuz.SylowEnum25002
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.InnerAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.SylowCheck

public section

namespace Certificates

open CertificateChecks

namespace Cert25002

open CFSG.EvenSporadicStandard.TwoSuz

noncomputable abbrev S : Subgroup GL12 :=
  Subgroup.closure {u | ∃ k < 4, vm u = ofMt (jMats.getD k oneM)}

noncomputable abbrev AB : Subgroup GL12 :=
  Subgroup.closure {u | vm u = ofMt matA ∨ vm u = ofMt matB}

end Cert25002

open CFSG.EvenSporadicStandard.TwoSuz Cert25002

end Certificates

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoSuz in
open CFSG.EvenSporadicStandard.TwoSuz Cert25002 in
theorem certificate25002 : Nat.card S = 2 ^ 14 ∧ (-1 : GL12) ∈ S ∧
    (∀ u : GL12, vm u = ofMt x1M → u ∈ S) ∧ (∀ u : GL12, vm u = ofMt x2M → u ∈ S) ∧
    rootCount S (-1) = 1056 ∧ (∀ u : GL12, vm u = ofMt x1M → rootCount S u = 384) ∧
    (∀ u : GL12, vm u = ofMt x2M → rootCount S u = 352) ∧ ofMt x2M = -ofMt x1M ∧
    (∀ s ∈ S, s * s = 1 → s ≠ 1 → s ≠ -1 →
      ∃ g ∈ AB, vm (g * s * g⁻¹) = ofMt x1M ∨ vm (g * s * g⁻¹) = ofMt x2M) ∧
    (∀ s ∈ S, ∃ i < (buildE sMats treePar).size,
      ofMt ((buildE sMats treePar).getD i oneM) = vm s) ∧
    ∀ i < (buildE sMats treePar).size,
      ∃ u ∈ S, vm u = ofMt ((buildE sMats treePar).getD i oneM) :=
  ⟨KernelSyl25002.card_sylS, KernelSyl25002.negOne_mem, fun _ hu => KernelSyl25002.x1_mem hu,
    fun _ hu => KernelSyl25002.x2_mem hu, KernelSyl25002.rootCount_negOne,
    fun _ hu => KernelSyl25002.rootCount_x1 hu, fun _ hu => KernelSyl25002.rootCount_x2 hu,
    KernelSyl25002.ofMt_x2M,
    fun _ hs hss hs1 hsz =>
      KernelSyl25002.cover (fun _ hu => Subgroup.subset_closure (Or.inl hu))
        (fun _ hu => Subgroup.subset_closure (Or.inr hu)) hs hss hs1 hsz,
    fun _ hs => KernelSyl25002.enum hs, fun _ hi => KernelSyl25002.enum_mem hi⟩

end Certificates

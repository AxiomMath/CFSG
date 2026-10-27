module

public import CFSG.HardMathSupport.Dickson.Bal207.D42TriDefs
import Certificates.Kernel.D42Tri.P0Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.Bal207.D42Tri CFSG.EvenSmallLie.OmegaEight in
theorem certificate17627 :
    (∀ a ∈ autT, a ^ 3 = 1 → a ∉ omegaT → ∃ y, (y = a ∨ y = a⁻¹) ∧
      ∃ g ∈ autT, g * y * g⁻¹ = CFSG.EvenSmallLie.OmegaEight.gen 8 ∨ g * y * g⁻¹ = t2Perm) ∧
    (∀ i, l0Gen i ∈ omegaT ∧ l0Gen i * CFSG.EvenSmallLie.OmegaEight.gen 8 = CFSG.EvenSmallLie.OmegaEight.gen 8 * l0Gen i) ∧
    (∀ r ∈ CFSG.Quasithin.u33PresRels, FreeGroup.lift l0Gen (FreeGroup.mk r) = 1) ∧
    l0Gen 0 ≠ 1 ∧
    CFSG.Sporadic.SmallOddCore.genOf 360 (k2Tbls ()) ≤
        CFSG.Sporadic.Schreier.centralizerIn omegaT t2Perm ∧
      Nat.card (CFSG.Sporadic.SmallOddCore.genOf 360 (k2Tbls ())) = 216 :=
  ⟨fun _ ha h3 hout => KernelD42Tri.p0_conj ha h3 hout, KernelD42Tri.p0_l0,
    KernelD42Tri.p0_l0_rel, KernelD42Tri.p0_l0_ne, KernelD42Tri.p0_k2⟩

end Certificates

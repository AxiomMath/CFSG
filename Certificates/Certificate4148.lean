module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerCheckInputs
public import CFSG.Sporadic.SmallOddCore.HeLocalCheckInputs
import Certificates.Kernel.LocalQT.He4148.First
import Certificates.Kernel.LocalQT.He4148.NoLayer

public section

namespace Certificates

open CertificateChecks.KernelLQT.He4148 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.HeInner in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native in
open CFSG.QuasithinUnique.Id2519.MathNoLayer CFSG.Sporadic.SmallOddCore in
open CFSG.ComponentClassification.PSL3Four in
theorem certificate4148 : (incListOK 8330 105 heDeltaP = true ∧
          ∀ j < 9, permChk 105 (heSigmaP.getD j #[]) = true ∧
            agreeOK 105 (heInnerC0 j) heDeltaP (heSigmaP.getD j #[]) = true)
    ∧ (heXp.check = true ∧ heXp.orderCertificate = 40320)
    ∧ (heDp.check = true ∧ heDp.orderCertificate = 20160)
    ∧ ((∀ k < 5, permChk 105 (heDpGens.getD k #[]) = true) ∧ heDpGens.length = 5 ∧
            heSigmaP.length = 9)
    ∧ ((∀ k < 5, heXp.sift (heDpPerm k) 0 = true) ∧
          (∀ i < 9, ∀ k < 5,
            heDp.sift (heSigmaPerm i * heDpPerm k * (heSigmaPerm i)⁻¹) 0 = true) ∧
          (∀ i < 9, ∀ k < 5,
            heDp.sift ((heSigmaPerm i)⁻¹ * heDpPerm k * heSigmaPerm i) 0 = true) ∧
          (∀ i < 9, ∀ j < 9,
            heDp.sift (heSigmaPerm i * heSigmaPerm j * (heSigmaPerm i)⁻¹ * (heSigmaPerm j)⁻¹) 0 =
              true))
    ∧ ((∀ j < 5, heDp.sift (permOrId 105 heDGens[j]!) 0 = true) ∧
          ClassCert 105 heDGens heDInvs heDEnum 10 heDClassWords heDClassSizes heDOrbits ∧
          (∀ j < heDGens.size, TabRep heDGens[j]! (permOrId 105 heDGens[j]!)) ∧
          heDEnum.tabs.size = 20160)
    ∧ (noLayerOK 42 (heToTabs he1E) (allTables heX1) = true) :=
  ⟨p105, xp_check, dp_check, dp_gens, dp_rel, dp_classes, he1_noLayer⟩

end Certificates

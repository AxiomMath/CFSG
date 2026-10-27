
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfA8Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.Census.CatFacts.C2008K1
import Certificates.Kernel.Census.CatFacts.C2008K2
import Certificates.Kernel.Census.CatFacts.C2008K3
import Certificates.Kernel.Census.CatFacts.C2008K4
import Certificates.Kernel.Census.CatFacts.C2008K5

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB in
theorem facts2008 : ((elemsT QS8).all (fun x => !(q0gens.all fun q =>
      QQ8.sift (x * q * x⁻¹) 0) || QQ8.sift x 0 || QQ8.sift (g08⁻¹ * x) 0) = true
    )
    ∧ ((q0gens.all fun q => decide (q * cfTau = cfTau * q) &&
      decide (q * cfZ = cfZ * q)) = true ∧ g08⁻¹ * cfZ * g08 = cfZ
    )
    ∧ ((elemsT QQ8).all (fun w => !QL8.sift w 0 || !decide (w * w = 1) ||
      decide (w = 1) || decide (w = cfZ) ||
      (elemsT QQ8).any (fun v => QL8.sift v 0 && !decide (w * v = v * w))) = true
    )
    ∧ (cfQH.check = true ∧ cfQH.orderCertificate = 64)
    ∧ (cfQR.check = true ∧ cfQR.orderCertificate = 128)
    ∧ ((elemsT QS8).all (fun x => !(cfHgens.all fun h =>
      cfQH.sift (x * h * x⁻¹) 0) || cfQR.sift x 0) = true
    )
    ∧ ((cfRgens.all fun x => QS8.sift x 0 &&
      decide (x * (cfTau * cfZ) = cfTau * cfZ * x)) = true ∧
      (elemsT cfQR).all (fun x => !(cfRgens.all fun g => decide (g * x = x * g)) ||
        decide (x = 1) || decide (x = cfTau * cfZ)) = true ∧
      cfQR.sift (cfTau * cfZ) 0 = true ∧ (cfTau * cfZ) * (cfTau * cfZ) = 1
    )
    ∧ (((elemsT QQ8).filter fun x => QL8.sift x 0).length = 8 ∧
      ((elemsT QL8).filter fun x => decide (x * cfTau = cfTau * x)).length = 24 ∧
      ((elemsT QS8).filter fun x => decide (x * (cfTau * cfZ) = cfTau * cfZ * x)).length =
        2 ^ 7 * 3 ∧
      ((elemsT cfQR).filter fun x => decide (x * cfZ = cfZ * x)).length = 64 ∧
      ((elemsT QS8).filter fun x => decide (x * cfZ = cfZ * x)).length = 2 ^ 6 * 3
    )
    ∧ ((q0gens.all fun q => QL8.sift q 0 || QL8.sift (q * cfTau⁻¹) 0 ||
      QL8.sift (q * s8⁻¹) 0 || QL8.sift (q * s8⁻¹ * cfTau⁻¹) 0) = true ∧
      QQ8.sift cfTau 0 = true ∧ QQ8.sift s8 0 = true
    )
    ∧ (cfQR.sift cfTzu 0 = true ∧ cfQR.sift cfTzv 0 = true ∧
      cfTzu * cfTzv * cfTzu⁻¹ * cfTzv⁻¹ = cfTau * cfZ ∧ QA8.sift cfK0 0 = true ∧
      cfK0⁻¹ * cfZ * cfK0 = cfTau
    )
    ∧ (cfQD1.check = true ∧ cfQD1.orderCertificate = 8 ∧ cfQD2.check = true ∧
      cfQD2.orderCertificate = 8 ∧ cfQD12.check = true ∧ cfQD12.orderCertificate = 64
    )
    ∧ (orderIs cfR1 4 = true ∧ orderIs cfR2 4 = true ∧ cfS1 * cfS1 = 1 ∧
      cfS2 * cfS2 = 1 ∧ cfS1 * cfR1 * cfS1⁻¹ = cfR1⁻¹ ∧ cfS2 * cfR2 * cfS2⁻¹ = cfR2⁻¹ ∧
      cfR1 * cfR1 = cfZ ∧ cfR2 * cfR2 = cfTau ∧ cfZ * cfZ = 1 ∧ cfTau * cfTau = 1 ∧
      ([cfR1, cfS1, cfR2, cfS2].all fun x => cfQR.sift x 0 && decide (x * cfZ = cfZ * x)) = true ∧
      ([cfR1, cfS1].all fun x => [cfR2, cfS2].all fun y => decide (y * x = x * y)) = true ∧
      ((List.range 4).all fun k => !decide (cfS1 = cfR1 ^ k)) = true ∧
      ((List.range 4).all fun k => !decide (cfS2 = cfR2 ^ k)) = true ∧
      (elemsT cfQD1).all (fun x => decide (x = 1) || !cfQD2.sift x 0) = true ∧
      (elemsT cfQD1).all (fun x => decide ((cfR1 * x = x * cfR1 ∧ cfS1 * x = x * cfS1) ↔
        (x = 1 ∨ x = cfZ))) = true ∧
      (elemsT cfQD2).all (fun x => decide ((cfR2 * x = x * cfR2 ∧ cfS2 * x = x * cfS2) ↔
        (x = 1 ∨ x = cfTau))) = true
    )
    ∧ (cfQF1.check = true ∧ cfQF1.orderCertificate = 16 ∧ cfQF2.check = true ∧
      cfQF2.orderCertificate = 16 ∧ cfQF3.check = true ∧ cfQF3.orderCertificate = 16 ∧
      cfQRz.check = true ∧ cfQRz.orderCertificate = 64
    )
    ∧ ((cfFgens.all fun x => cfQR.sift x 0 && decide (x * cfZ = cfZ * x)) = true ∧
      (elemsT cfQF1).all (fun x => decide (x * x = 1)) = true ∧
      (elemsT cfQF2).all (fun x => decide (x * x = 1)) = true ∧
      (elemsT cfQF3).all (fun x => decide (x * x = 1)) = true ∧
      cfQRz.sift cfZ 0 = true ∧ cfQRz.sift cfTau 0 = true ∧ cfQRz.sift cfR1 0 = true ∧
      cfQRz.sift cfR2 0 = true ∧ (cfFgens.all fun x => decide (x * cfZ = cfZ * x) &&
        decide (x * cfTau = cfTau * x)) = true ∧
      (elemsT cfQRz).all (fun x => !(cfFgens.all fun g => decide (g * x = x * g)) ||
        (decide (x = 1) || decide (x = cfZ) || decide (x = cfTau) || decide (x = cfZ * cfTau))) =
        true ∧
      (elemsT cfQRz).all (fun x => decide (x * x = 1) || decide (x * x = cfZ) ||
        decide (x * x = cfTau) || decide (x * x = cfZ * cfTau)) = true
    )
    ∧ (cfQE.check = true ∧ cfQE.orderCertificate = 16)
    ∧ ((cfEgens.all fun x => cfQR.sift x 0 && QA8.sift x 0) = true ∧
      (elemsT cfQE).all (fun x => decide (x * x = 1)) = true ∧ cfQE.sift cfZ 0 = true ∧
      cfQE.sift cfTau 0 = true
    )
    ∧ (((elemsT cfQR).filter fun x => QA8.sift x 0).all (fun x =>
      !decide (x * x = 1) || cfQE.sift x 0 || decide ((((elemsT cfQR).filter fun x =>
        QA8.sift x 0).filter fun y => decide (y * y = 1) && decide (y * x = x * y)).length <
          16)) = true
    )
    ∧ ((elemsT QS8).all (fun x => !(cfEgens.all fun e =>
      decide (e * x = x * e)) || cfQE.sift x 0) = true
    )
    ∧ ((cfOz.all fun p => decide (p.2⁻¹ * cfZ * p.2 = p.1) && QS8.sift p.2 0 &&
        (cfEgens.all fun e => cfQE.sift (p.2 * e * p.2⁻¹) 0)) = true ∧
      (cfOzt.all fun p => decide (p.2⁻¹ * (cfZ * cfTau) * p.2 = p.1) && QS8.sift p.2 0 &&
        (cfEgens.all fun e => cfQE.sift (p.2 * e * p.2⁻¹) 0)) = true ∧
      (cfOz.map Prod.fst).Nodup ∧ (cfOzt.map Prod.fst).Nodup ∧
      (elemsT cfQE).all (fun w => decide (w = 1) || decide (w ∈ cfOz.map Prod.fst) ||
        decide (w ∈ cfOzt.map Prod.fst)) = true ∧
      (cfOz.all fun p => cfQE.sift p.1 0) = true ∧ (cfOzt.all fun p => cfQE.sift p.1 0) = true
    )
    ∧ ((elemsT QS8).all (fun x => !(cfEgens.all fun e =>
        cfQE.sift (x * e * x⁻¹) 0) || (decide (x⁻¹ * cfZ * x ∈ cfOz.map Prod.fst) &&
        decide (x⁻¹ * (cfZ * cfTau) * x ∈ cfOzt.map Prod.fst))) = true ∧
      ((elemsT QS8).filter fun x => cfEgens.all fun e => cfQE.sift (x * e * x⁻¹) 0).length =
        1152
    )
    ∧ ((cfEgens.all fun x => (cfOz.map Prod.fst).any fun u =>
      (cfOz.map Prod.fst).any fun v => decide (x = u * v)) = true
    )
    ∧ ((elemsT cfQR).all (fun w => !decide (w * w = 1) || QA8.sift w 0 ||
      (fun y => decide (y ∈ cfCls1C)) w ||
      (elemsT cfQR).any (fun r => !decide (w * (r * w * r⁻¹) = r * w * r⁻¹ * w)) ||
      decide (((elemsT cfQR).filter fun y => decide (y * y = 1) &&
        !(fun y => decide (y ∈ cfCls1C)) y &&
        (elemsT cfQR).all fun r => decide (y * (r * w * r⁻¹) = r * w * r⁻¹ * y)).length < 16)) =
        true
    )
    ∧ ((elemsT cfQE).all (fun e => decide (e * s8 * e⁻¹ * s8⁻¹ = 1) ||
        decide (e * s8 * e⁻¹ * s8⁻¹ = cfCE)) = true ∧ s8 * s8 = 1 ∧
      cfQE.sift cfE1 0 = true ∧ cfE1 * s8 * cfE1⁻¹ * s8⁻¹ = cfCE ∧ cfCE * cfCE = 1 ∧
      cfCE ≠ 1 ∧ cfQR.sift cfEe 0 = true ∧ QA8.sift cfEe 0 = true ∧
      cfEn1 * cfEn2 * cfEn1⁻¹ * cfEn2⁻¹ = cfEe ∧ cfEe * cfEe = 1 ∧
      (cfEgens.all fun g => decide (g * cfEe = cfEe * g)) = false ∧ QS8.sift cfEn1 0 = true ∧
      QS8.sift cfEn2 0 = true ∧ (cfEgens.all fun e => cfQE.sift (cfEn1 * e * cfEn1⁻¹) 0) = true ∧
      (cfEgens.all fun e => cfQE.sift (cfEn2 * e * cfEn2⁻¹) 0) = true
    )
    ∧ ((elemsT QS8).all (fun y => !decide (y * y = 1) || QA8.sift y 0 ||
      decide (y ∈ cfCls1C) || decide (y ∈ cfCls2C)) = true ∧
      (elemsT QA8).all (fun y => !decide (y * y = 1) || decide (y = 1) ||
        decide (y ∈ cfICls1C) || decide (y ∈ cfICls2C)) = true
    )
    ∧ ((elemsT cfQR).all (fun x => !decide (x * x = 1) || decide (x = 1) ||
      decide (x ∈ cfB) || decide (((elemsT cfQR).filter fun y => decide (y * y = 1) &&
        decide (y * x = x * y)).length < 32)) = true
    ) := by
  refine ⟨?_, cfComm2008K, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    cfEwit2008K, ?_, ?_, ?_, ?_⟩
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfCoset2008K
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfZ2008K
  · exact ⟨check_certificate_of _ _ _ _ _ cfQH2008K.1,
      (orderCertificate_eq_orderV _).trans cfQH2008K.2⟩
  · exact ⟨check_certificate_of _ _ _ _ _ cfQR2008K.1,
      (orderCertificate_eq_orderV _).trans cfQR2008K.2⟩
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfNorm2008K
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfR2008K
  · simp only [elemsT_eq_elemsV, sift_eq_siftP]
    exact ⟨cfCardR2008K.1, cfCardR2008K.2.1, cfCardS2008K.1, cfCardR2008K.2.2, cfCardS2008K.2⟩
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfQeq2008K
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfElt2008K
  · exact ⟨check_certificate_of _ _ _ _ _ cfQD2008K.1,
      (orderCertificate_eq_orderV _).trans cfQD2008K.2.1,
      check_certificate_of _ _ _ _ _ cfQD2008K.2.2.1,
      (orderCertificate_eq_orderV _).trans cfQD2008K.2.2.2.1,
      check_certificate_of _ _ _ _ _ cfQD2008K.2.2.2.2.1,
      (orderCertificate_eq_orderV _).trans cfQD2008K.2.2.2.2.2⟩
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfD2008K
  · exact ⟨check_certificate_of _ _ _ _ _ cfQF2008K.1,
      (orderCertificate_eq_orderV _).trans cfQF2008K.2.1,
      check_certificate_of _ _ _ _ _ cfQF2008K.2.2.1,
      (orderCertificate_eq_orderV _).trans cfQF2008K.2.2.2.1,
      check_certificate_of _ _ _ _ _ cfQF2008K.2.2.2.2.1,
      (orderCertificate_eq_orderV _).trans cfQF2008K.2.2.2.2.2.1,
      check_certificate_of _ _ _ _ _ cfQF2008K.2.2.2.2.2.2.1,
      (orderCertificate_eq_orderV _).trans cfQF2008K.2.2.2.2.2.2.2⟩
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfF2008K
  · exact ⟨check_certificate_of _ _ _ _ _ cfQE2008K.1,
      (orderCertificate_eq_orderV _).trans cfQE2008K.2⟩
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfE2008K
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfEUniq2008K
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfECent2008K
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfOrb2008K
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfOrb22008K
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfNormal2008K
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfMisc2008K
  · simp only [elemsT_eq_elemsV, sift_eq_siftP]
    exact ⟨cfOuterS2008K, cfOuterA2008K⟩
  · simpa only [elemsT_eq_elemsV, sift_eq_siftP] using cfE322008K

end CertificateChecks.KernelCatFacts

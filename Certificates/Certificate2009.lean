
module

public import Certificates.Certificate2009Base

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfP45Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
import Certificates.Kernel.Census.CatFacts.C2009

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB in

theorem certificate2009 : ((elemsT QA45).all (fun x => !(q0gens.all fun q =>
      QQ45.sift (x * q * x⁻¹) 0) || QQ45.sift x 0 || QQ45.sift (g045⁻¹ * x) 0) = true
    )
    ∧ ((q0gens.all fun q => decide (q * cfTau = cfTau * q) &&
      decide (q * cfZ = cfZ * q)) = true ∧ g045⁻¹ * cfZ * g045 = cfZ
    )
    ∧ ((elemsT QQ45).all (fun w => !QL45.sift w 0 || !decide (w * w = 1) ||
      decide (w = 1) || decide (w = cfZ) ||
      (elemsT QQ45).any (fun v => QL45.sift v 0 && !decide (w * v = v * w))) = true
    )
    ∧ (cfQH.check = true ∧ cfQH.orderCertificate = 64)
    ∧ (cfQR.check = true ∧ cfQR.orderCertificate = 128)
    ∧ ((elemsT QA45).all (fun x => !(cfHgens.all fun h =>
      cfQH.sift (x * h * x⁻¹) 0) || cfQR.sift x 0) = true
    )
    ∧ ((cfRgens.all fun x => QA45.sift x 0 &&
      decide (x * (cfTau * cfZ) = cfTau * cfZ * x)) = true ∧
      (elemsT cfQR).all (fun x => !(cfRgens.all fun g => decide (g * x = x * g)) ||
        decide (x = 1) || decide (x = cfTau * cfZ)) = true ∧
      cfQR.sift (cfTau * cfZ) 0 = true ∧ (cfTau * cfZ) * (cfTau * cfZ) = 1
    )
    ∧ (((elemsT QQ45).filter fun x => QL45.sift x 0).length = 8 ∧
      ((elemsT QL45).filter fun x => decide (x * cfTau = cfTau * x)).length = 24 ∧
      ((elemsT QA45).filter fun x => decide (x * (cfTau * cfZ) = cfTau * cfZ * x)).length =
        2 ^ 7 * 9 ∧
      ((elemsT cfQR).filter fun x => decide (x * cfZ = cfZ * x)).length = 64 ∧
      ((elemsT QA45).filter fun x => decide (x * cfZ = cfZ * x)).length = 2 ^ 6 * 3
    )
    ∧ ((q0gens.all fun q => QL45.sift q 0 || QL45.sift (q * cfTau⁻¹) 0 ||
      QL45.sift (q * s045⁻¹) 0 || QL45.sift (q * s045⁻¹ * cfTau⁻¹) 0) = true ∧
      QQ45.sift cfTau 0 = true ∧ QQ45.sift s045 0 = true
    )
    ∧ (cfQR.sift cfTzu 0 = true ∧ cfQR.sift cfTzv 0 = true ∧
      cfTzu * cfTzv * cfTzu⁻¹ * cfTzv⁻¹ = cfTau * cfZ ∧ QP45.sift cfK0 0 = true ∧
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
    ∧ ((cfEgens.all fun x => cfQR.sift x 0 && QP45.sift x 0) = true ∧
      (elemsT cfQE).all (fun x => decide (x * x = 1)) = true ∧ cfQE.sift cfZ 0 = true ∧
      cfQE.sift cfTau 0 = true
    )
    ∧ (((elemsT cfQR).filter fun x => QP45.sift x 0).all (fun x =>
      !decide (x * x = 1) || cfQE.sift x 0 || decide ((((elemsT cfQR).filter fun x =>
        QP45.sift x 0).filter fun y => decide (y * y = 1) && decide (y * x = x * y)).length <
          16)) = true
    )
    ∧ ((elemsT QA45).all (fun x => !(cfEgens.all fun e =>
      decide (e * x = x * e)) || cfQE.sift x 0) = true
    )
    ∧ ((cfOz.all fun p => decide (p.2⁻¹ * cfZ * p.2 = p.1) && QA45.sift p.2 0 &&
        (cfEgens.all fun e => cfQE.sift (p.2 * e * p.2⁻¹) 0)) = true ∧
      (cfOzt.all fun p => decide (p.2⁻¹ * (cfZ * cfTau) * p.2 = p.1) && QA45.sift p.2 0 &&
        (cfEgens.all fun e => cfQE.sift (p.2 * e * p.2⁻¹) 0)) = true ∧
      (cfOz.map Prod.fst).Nodup ∧ (cfOzt.map Prod.fst).Nodup ∧
      (elemsT cfQE).all (fun w => decide (w = 1) || decide (w ∈ cfOz.map Prod.fst) ||
        decide (w ∈ cfOzt.map Prod.fst)) = true ∧
      (cfOz.all fun p => cfQE.sift p.1 0) = true ∧ (cfOzt.all fun p => cfQE.sift p.1 0) = true
    )
    ∧ ((elemsT QA45).all (fun x => !(cfEgens.all fun e =>
        cfQE.sift (x * e * x⁻¹) 0) || (decide (x⁻¹ * cfZ * x ∈ cfOz.map Prod.fst) &&
        decide (x⁻¹ * (cfZ * cfTau) * x ∈ cfOzt.map Prod.fst))) = true ∧
      ((elemsT QA45).filter fun x => cfEgens.all fun e => cfQE.sift (x * e * x⁻¹) 0).length =
        1920
    )
    ∧ ((cfEgens.all fun x => decide (x ∈ cfOzt.map Prod.fst)) = true)
    ∧ ((elemsT cfQR).all (fun w => !decide (w * w = 1) || QP45.sift w 0 ||
      (fun y => decide (y ∈ cfCls1C)) w ||
      (elemsT cfQR).any (fun r => !decide (w * (r * w * r⁻¹) = r * w * r⁻¹ * w)) ||
      decide (((elemsT cfQR).filter fun y => decide (y * y = 1) &&
        !(fun y => decide (y ∈ cfCls1C)) y &&
        (elemsT cfQR).all fun r => decide (y * (r * w * r⁻¹) = r * w * r⁻¹ * y)).length < 16)) =
        true
    )
    ∧ ((elemsT cfQE).all (fun e => decide (e * s045 * e⁻¹ * s045⁻¹ = 1) ||
        decide (e * s045 * e⁻¹ * s045⁻¹ = cfCE)) = true ∧ s045 * s045 = 1 ∧
      cfQE.sift cfE1 0 = true ∧ cfE1 * s045 * cfE1⁻¹ * s045⁻¹ = cfCE ∧ cfCE * cfCE = 1 ∧
      cfCE ≠ 1 ∧ cfQR.sift cfEe 0 = true ∧ QP45.sift cfEe 0 = true ∧
      cfEn1 * cfEn2 * cfEn1⁻¹ * cfEn2⁻¹ = cfEe ∧ cfEe * cfEe = 1 ∧
      (cfEgens.all fun g => decide (g * cfEe = cfEe * g)) = false ∧ QA45.sift cfEn1 0 = true ∧
      QA45.sift cfEn2 0 = true ∧ (cfEgens.all fun e => cfQE.sift (cfEn1 * e * cfEn1⁻¹) 0) = true ∧
      (cfEgens.all fun e => cfQE.sift (cfEn2 * e * cfEn2⁻¹) 0) = true
    )
    ∧ ((elemsT QA45).all (fun y => !decide (y * y = 1) || QP45.sift y 0 ||
      decide (y ∈ cfCls1C) || decide (y ∈ cfCls2C)) = true ∧
      (elemsT QP45).all (fun y => !decide (y * y = 1) || decide (y = 1) ||
        decide (y ∈ cfICls1C) || decide (y ∈ cfICls2C)) = true
    )
    ∧ ((elemsT cfQR).all (fun x => !decide (x * x = 1) || decide (x = 1) ||
      decide (x ∈ cfB) || decide (((elemsT cfQR).filter fun y => decide (y * y = 1) &&
        decide (y * x = x * y)).length < 32)) = true
    ) := KernelCatFacts.facts2009

end Certificates

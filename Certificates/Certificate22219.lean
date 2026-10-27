
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs
import Certificates.Kernel.L34Cov.Facts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase

public section

namespace Certificates

open CertificateChecks

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four in
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable in
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real in
theorem certificate22219 :
    (∀ k < 64, ∀ l < 64, (t1Entry k l).1 < 64 ∧ (t1Entry k l).2.1 < 4 ∧
      (t1Entry k l).2.2.1 < 4 ∧ (t1Entry k l).2.2.2 < 3 ∧
      cv (tw k) * cv (tw l) = cv (tw (t1Entry k l).1) * cv (zOf (t1Entry k l))) ∧
    (∀ i < 36,
      abPerm (uA i) = CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i * aS * (CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i)⁻¹ ∧
      abPerm (uB i) = CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i * bS * (CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i)⁻¹ ∧
      (∀ k < 64, ((alphaEntry i k).1 < 64 ∧ (alphaEntry i k).2.1 < 4 ∧
          (alphaEntry i k).2.2.1 < 4 ∧ (alphaEntry i k).2.2.2 < 3) ∧
        CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i * wordPerm (tg k) * (CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i)⁻¹ = wordPerm (tg (alphaEntry i k).1) ∧
        cv (substWord (CFSG.ComponentClassification.GrSLit.L34Facts.Real.aut i) (tw k)) = cv (tw (alphaEntry i k).1) * cv (zOf (alphaEntry i k))) ∧
      (∀ j < 2, ((alphaEntry i (64 + j)).1 < 64 ∧ (alphaEntry i (64 + j)).2.1 < 4 ∧
          (alphaEntry i (64 + j)).2.2.1 < 4 ∧ (alphaEntry i (64 + j)).2.2.2 < 3) ∧
        (alphaEntry i (64 + j)).1 = 0 ∧
        cv (substWord (CFSG.ComponentClassification.GrSLit.L34Facts.Real.aut i) (zGen j)) = cv (zOf (alphaEntry i (64 + j))))) ∧
    (∀ y ∈ R, (∀ t ∈ T0, y * t * y⁻¹ ∈ T0) →
      ∃ i < 36, ∃ t < 64, y = wordPerm (tg t) * CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i) := KernelL34Cov.facts22219

end Certificates

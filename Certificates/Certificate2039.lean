module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAutInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovals
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignWittUnique
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Actions
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovals
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAutInputs
import all CFSG.Fischer.F4
import Certificates.Kernel.LocalComp.M22ParitySigma
import Certificates.Certificate2195

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign MulAction
open CFSG.Monster.B.Classical.Plane
open scoped Pointwise

namespace CertificateChecks.Batch2039

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign MulAction
open CFSG.Monster.B.Classical.Plane
open scoped Pointwise

theorem phi_facts_0 : (∀ y, psiFun y ≠ 0 ∧ phiFun (psiFun y) = y) ∧
    (∀ x, x ≠ 0 → psiFun (phiFun x) = x) ∧ (∀ x, sigmaFun (sigmaFun x) = x) ∧
    hexadList.all (fun B => !(decide ((0 : Fin 22) ∈ B)) ||
      ((B.erase 0).image phiFun ∈ Finset.univ.image projLine)) = true ∧
    hexadList.all (fun B => decide ((0 : Fin 22) ∈ B) ||
      hyperClass0.contains (B.image phiFun)) = true ∧
    (∀ a : Fin 21, hexadList.any fun B =>
      decide ((0 : Fin 22) ∈ B) && ((B.erase 0).image phiFun == projLine a)) ∧
    hyperClass0.all (fun X => hexadList.any fun B =>
      !(decide ((0 : Fin 22) ∈ B)) && (B.image phiFun == X)) = true ∧
    hexadList.all (fun B => hexadMasks.contains (mask (B.image sigmaFun))) = true := by
  decide +kernel

theorem class_images_2 : (hyperClass0.toFinset.image fun X => X.image (ofTable21 deltaTab)) =
      hyperClass1.toFinset ∧
    (hyperClass1.toFinset.image fun X => X.image (ofTable21 deltaTab)) = hyperClass2.toFinset ∧
    hyperClass0.toFinset ≠ hyperClass1.toFinset ∧ hyperClass0.toFinset ≠ hyperClass2.toFinset ∧
    hyperClass1.toFinset ≠ hyperClass2.toFinset := by
  decide +kernel

theorem hexad0_card_3 : hexad0.card = 6 := by
  decide +kernel

end CertificateChecks.Batch2039

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign MulAction in
open CFSG.Monster.B.Classical.Plane in
open scoped Pointwise in
theorem certificate2039 : ((∀ y, psiFun y ≠ 0 ∧ phiFun (psiFun y) = y) ∧
      (∀ x, x ≠ 0 → psiFun (phiFun x) = x) ∧ (∀ x, sigmaFun (sigmaFun x) = x) ∧
      hexadList.all (fun B => !(decide ((0 : Fin 22) ∈ B)) ||
        ((B.erase 0).image phiFun ∈ Finset.univ.image projLine)) = true ∧
      hexadList.all (fun B => decide ((0 : Fin 22) ∈ B) ||
        hyperClass0.contains (B.image phiFun)) = true ∧
      (∀ a : Fin 21, hexadList.any fun B =>
        decide ((0 : Fin 22) ∈ B) && ((B.erase 0).image phiFun == projLine a)) ∧
      hyperClass0.all (fun X => hexadList.any fun B =>
        !(decide ((0 : Fin 22) ∈ B)) && (B.image phiFun == X)) = true ∧
      hexadList.all (fun B => hexadMasks.contains (mask (B.image sigmaFun))) = true
    )
    ∧ (m22Count (fun g => ∀ x, g x = sigmaFun x) = 0)
    ∧ ((hyperClass0.toFinset.image fun X => X.image (ofTable21 deltaTab)) =
        hyperClass1.toFinset ∧
      (hyperClass1.toFinset.image fun X => X.image (ofTable21 deltaTab)) = hyperClass2.toFinset ∧
      hyperClass0.toFinset ≠ hyperClass1.toFinset ∧ hyperClass0.toFinset ≠ hyperClass2.toFinset ∧
      hyperClass1.toFinset ≠ hyperClass2.toFinset
    )
    ∧ (hexad0.card = 6) :=
  ⟨CertificateChecks.Batch2039.phi_facts_0, KernelLC.m22Count_sigma, CertificateChecks.Batch2039.class_images_2,
    CertificateChecks.Batch2039.hexad0_card_3⟩

end Certificates

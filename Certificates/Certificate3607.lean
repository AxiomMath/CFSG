module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAElt
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain
import Certificates.Kernel.UnitarySix.Sec3.Sound.Elt3607

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.Monster.B.Co2 in
theorem certificate3607 : (∀ x ∈ chZ2S.grp, ∃ a, Rep 693 a x ∧ c11aAt a = true)
    ∧ (∀ x ∈ chLam.grp, ∃ a, Rep 693 a x ∧ c6At a = true)
    ∧ (∀ x ∈ chLam.grp, ∀ y ∈ chSig.grp, ∃ a b, Rep 693 a x ∧ Rep 693 b y ∧ c7At a b = true)
    ∧ (∀ x ∈ chSig.grp, ∃ a, Rep 693 a x ∧ c9At a = true)
    ∧ (i5GenCheck = true)
    ∧ (∀ x ∈ chT1.grp, ∃ a, Rep 693 a x ∧ i5At a = true)
    ∧ (i8GenCheck = true)
    ∧ (∀ x ∈ chX1.grp, ∀ y ∈ chX3.grp, ∃ a b, Rep 693 a x ∧ Rep 693 b y ∧ i8At a b = true)
    ∧ (i8bGenCheck = true)
    ∧ (∀ x ∈ chX3.grp, ∃ a, Rep 693 a x ∧ i8bAt a = true)
    ∧ (nmCheck = true)
    ∧ (chX3A3.ok = true)
    ∧ (chX3A3.order = 8192)
    ∧ (chSigA3.ok = true)
    ∧ (chSigA3.order = 24576) :=
  ⟨c11a_k', c6_k', c7_k', c9_k', i5Gen_k', i5_k', i8Gen_k', i8_k', i8bGen_k', i8b_k', nm_k',
    chX3A3_k'.1, chX3A3_k'.2, chSigA3_k'.1, chSigA3_k'.2⟩

end Certificates

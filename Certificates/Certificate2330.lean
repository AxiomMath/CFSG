module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBCheckInputs
import Certificates.Kernel.LocalComp.HeFix2330.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.HeldFix CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Monster.B.Co2.Native in
theorem certificate2330 :
    (∀ i < 2, ∀ j ∈ hfQWords.getD i [], j < 9) ∧ (∀ i < 6, ∀ j ∈ hfCommWords.getD i [], j < 9) ∧
      (∀ i < 2, ∀ j ∈ hfOrd7Words.getD i [], j < 9) ∧
      (∀ i < 3, ∀ j ∈ hfOrd3Words.getD i [], j < 9) ∧
      isInvA 8330 (hfCTab (hfQWords.getD 0 [])) (invCand 8330 (hfCTab (hfQWords.getD 0 []))) =
        true ∧
      isInvA 8330 (hfCTab (hfQWords.getD 1 [])) (invCand 8330 (hfCTab (hfQWords.getD 1 []))) =
        true ∧
      comp 8330 (comp 8330 (comp 8330 (hfCTab (hfQWords.getD 0 [])) (hfCTab (hfQWords.getD 1 [])))
        (invCand 8330 (hfCTab (hfQWords.getD 0 [])))) (invCand 8330 (hfCTab (hfQWords.getD 1 []))) =
        heT1Arr ∧
      (∀ i < 2, hfCTab (hfRep 7 (hfOrd7Words.getD i [])) = idTab 8330 ∧
        hfCTab (hfOrd7Words.getD i []) ≠ idTab 8330) ∧
      (∀ i < 3, hfCTab (hfRep 3 (hfOrd3Words.getD i [])) = idTab 8330 ∧
        hfCTab (hfOrd3Words.getD i []) ≠ idTab 8330) ∧
      (∀ i < 6, comp 42 (invTab 42 (hfCTab42 (hfCommWords.getD i [])))
        (hfCTab42 (hfCommWords.getD i [])) = idTab 42 ∧
        (invTab 42 (hfCTab42 (hfCommWords.getD i []))).size = 42) ∧
      enumOK 42 hfCommTabs42 hfCommEnum42 = true ∧ hfCommEnum42.tabs.size = 10752 ∧
      enumOK 42 hfOrd7Tabs42 hfOrd7Enum42 = true ∧ hfOrd7Enum42.tabs.size = 10752 ∧
      enumOK 42 hfOrd3Tabs42 hfOrd3Enum42 = true ∧ hfOrd3Enum42.tabs.size = 10752 := KernelLC.HeFix2330.check

end Certificates

end

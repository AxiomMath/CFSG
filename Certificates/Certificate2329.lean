
module


public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs
import Certificates.Kernel.LocalComp.HeFix2329.Grp

public section

namespace Certificates

open CertificateChecks.KernelLC.HeFix2329 CertificateChecks.KernelLC.HeFix

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.HeldFix CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2329 : (

    (∀ j < 9, (hfC1Tabs[j]!).size = 8330) ∧ heT1Arr.size = 8330 ∧ hfXTab.size = 8330 ∧
      lettersOK 3 hfXWord = true ∧
      (∀ i < 4, ∀ j ∈ hfTauWords.getD i [], j < 9) ∧ (∀ j ∈ hfYWord, j < 10) ∧
      (∀ i < 6, ∀ j ∈ hfEWords.getD i [], j < 5) ∧
      siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0 hfYTab = false ∧
      enumOK 8330 hfT0Tabs hfT0Enum = true ∧ hfT0Enum.tabs.size = 2048 ∧
      (∀ j < 6, ∀ x ∈ hfDelta32, (hfT0Tabs[j]!)[x]! ∈ hfDelta32) ∧
      (List.range 8330).countP (fun i => hfEATab[i]! == i) = 346 
)
    ∧ (

    hfDelta32.length = 32 ∧ (∀ x ∈ hfDelta32, x < 8330) ∧ hfDelta32.Nodup 
)
    ∧ (

    enumOK 32 hfTTabs32 hfTEnum32 = true ∧ hfTEnum32.tabs.size = 1024 ∧
      enumOK 32 hfT0Tabs32 hfT0Enum32 = true ∧ hfT0Enum32.tabs.size = 2048 ∧
      (hfTEnum32.tabs.toList.filter (commAll 32 hfTTabs32)).length = 2 ∧
      enumOK 32 hfETabs32 hfEEnum32 = true ∧ hfEEnum32.tabs.size = 64 ∧
      (∀ i < 6, ∀ j < 6, comp 32 hfETabs32[i]! hfETabs32[j]! =
        comp 32 hfETabs32[j]! hfETabs32[i]!) ∧
      (∀ i < 6, comp 32 hfETabs32[i]! hfETabs32[i]! = idTab 32) ∧
      normalOK 32 hfEEnum32.tabs hfTTabs32 (hfTTabs32.map (invTab 32)) hfETabs32 = true ∧
      hfOuterE8Check 32 hfTEnum32.tabs hfT0Enum32.tabs = true 
) :=
  ⟨⟨fun _ hj => c1_size hj, t1_size, x_size, lettersX, tau_lt, yw_lt, by decide, siftY_false,
      enumT0_ok.1, enumT0_ok.2, hfDelta_pres, hfFix346⟩, hfDelta32_facts, hfSylow32_true⟩

end Certificates

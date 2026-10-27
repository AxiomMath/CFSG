
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
import Certificates.Kernel.L34Cov.Facts22201

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four in
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable in
open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22201 :
    (invsOK 42 #[aST, bST] #[invTab 42 aST, invTab 42 bST] &&
      rels.all (fun r => abTab r == idTab 42) &&
      coverWs.all (fun r => abTab r == idTab 42) &&
      (abTab zOne == idTab 42 && abTab zTwo == idTab 42 && abTab zThree == idTab 42) &&
      !(bST == idTab 42) &&
      (abTab (genABWords.getD 0 []) == g₁T && abTab (genABWords.getD 1 []) == g₂T &&
        abTab (genABWords.getD 2 []) == g₃T) &&
      (abTab uAU == conjTab 42 r₄T r₄T aST && abTab uBU == conjTab 42 r₄T r₄T bST) &&
      (abTab uAF == conjTab 42 r₂T r₂T aST && abTab uBF == conjTab 42 r₂T r₂T bST) &&
      (abTab uAG == conjTab 42 r₃T r₃T aST && abTab uBG == conjTab 42 r₃T r₃T bST) &&
      (allBelow 64 fun k => abTab (tw k) == wordTab (tg k) &&
        found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs) (enumBFS 42 (wordTabs wT₀) 64).tabs
          (wordTab (tg k))) &&
      (allBelow 64 fun k => allBelow k fun l => !(wordTab (tg k) == wordTab (tg l))) &&
      (allBelow 64 fun k => (comp 42 (wordTab (tg k)) (wordTab (tg k)) == idTab 42) ==
        (k == 0 || (sqData.map (·.1)).contains k)) &&
      (allBelow 64 fun k => found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs)
        (enumBFS 42 (wordTabs wT₀) 64).tabs (conjTab 42 r₄T r₄T (wordTab (tg k)))) &&
      (allBelow 64 fun k => (comp 42 (wordTab (tg k)) r₄T == comp 42 r₄T (wordTab (tg k))) ==
        q8Idx.contains k) &&
      countBelow 64 (fun k => comp 42 (wordTab (tg k)) (conjTab 42 r₄T r₄T (wordTab (tg k))) ==
        idTab 42) == 8 &&
      (witnessOK witnessF r₂T && witnessOK witnessG r₃T && witnessOK witnessU r₄T)) = true ∧
    ∀ s ∈ coverSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2)) := KernelL34Cov.facts22201

end Certificates

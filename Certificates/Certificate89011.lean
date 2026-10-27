module

public import Certificates.Data.CFSGNative.AS91.M24Geom
import CFSG.Certificates.Kernel.M24G.PairsCount
import Certificates.Kernel.M24G.OctChecks
import Certificates.Kernel.M24G.TrioChecks
import Certificates.Kernel.M24G.SextChecks
import Certificates.Kernel.M24G.TrioReplay
import Certificates.Kernel.M24G.SextReplay
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.Batch89011

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

private theorem octSteps_eq : Native.genTabs.map Native.img = [imgF OctD.bA, imgF OctD.bB, imgF OctD.bBi] := by
  have h := OctC.tabs_eq
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨hA, hB, hBi⟩ := h
  have lA : ∀ x ∈ Native.pATab.toList, x < 24 := by decide
  have lB : ∀ x ∈ Native.pBTab.toList, x < 24 := by decide
  have lBi : ∀ x ∈ Native.pBiTab.toList, x < 24 := by decide
  simp only [Native.genTabs, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨funext fun m => ?_, funext fun m => ?_, funext fun m => ?_⟩
  · rw [img_eq_imgF _ lA, hA]
  · rw [img_eq_imgF _ lB, hB]
  · rw [img_eq_imgF _ lBi, hBi]

private theorem check_holds : Native.listChecks () = true := by
  have hO : replayOK id (Native.genTabs.map Native.img) 255 1000 OctD.O OctD.par OctD.gen
      (posTree id OctD.O) = true := by
    rw [octSteps_eq]
    exact OctC.replay
  have hT : replayOK Native.key3 (Native.genTabs.map Native.imgTrio) Native.baseTrio 5000 TL tPar
      tGen (posTree Native.key3 TL) = true := by
    rw [trioSteps_eq]
    exact trioReplay_ok
  have hS : replayOK Native.keyL (Native.genTabs.map Native.imgSext) Native.baseSext 3000 SL sPar
      sGen (posTree Native.keyL SL) = true := by
    rw [sextSteps_eq]
    exact sextReplay_ok
  exact listChecks_of_replay hO hT hS OctC.length TrioC.length SextC.length OctC.items TrioC.items
    SextC.items OctC.base (pairsOK_of_count hO OctC.length OctC.base hT TrioC.length TrioC.items
      TrioC.count) SextC.tets

end CertificateChecks.Batch89011

namespace Certificates

open CertificateChecks

theorem certificate89011 : CFSG.Quasithin.H13.AS91.M24G.Native.listChecks () = true :=
  CertificateChecks.Batch89011.check_holds

end Certificates

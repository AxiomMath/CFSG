module

public import Certificates.Data.CFSGNative.AS91.M24Trio
import CFSG.Certificates.Kernel.M24G.Trio12Sound
import Certificates.Kernel.M24G.OctChecks
import Certificates.Kernel.M24G.TrioChecks
import Certificates.Kernel.M24G.SextChecks
import Certificates.Kernel.M24G.TrioReplay
import Certificates.Kernel.M24G.SextReplay
import Certificates.Kernel.M24G.Trio12Checks
import Certificates.Kernel.M24G.Trio12Close
import Certificates.Kernel.M24G.Trio12Orb
import Certificates.Kernel.M24G.Trio12Tup
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.Batch89018

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

private theorem check_holds : Native.trio12Check () = true := by
  have hOs : Native.genTabs.map Native.img = [imgF OctD.bA, imgF OctD.bB, imgF OctD.bBi] := by
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
  have hO : replayOK id (Native.genTabs.map Native.img) 255 1000 OctD.O OctD.par OctD.gen
      (posTree id OctD.O) = true := by
    rw [hOs]
    exact OctC.replay
  have hT : replayOK Native.key3 (Native.genTabs.map Native.imgTrio) Native.baseTrio 5000 TL tPar
      tGen (posTree Native.key3 TL) = true := by
    rw [trioSteps_eq]
    exact trioReplay_ok
  have hS : replayOK Native.keyL (Native.genTabs.map Native.imgSext) Native.baseSext 3000 SL sPar
      sGen (posTree Native.keyL SL) = true := by
    rw [sextSteps_eq]
    exact sextReplay_ok
  have h0T : TL.getD 0 default = Native.baseTrio := by
    have hb := (replay_facts hT).2.1
    generalize TL = L at hb ⊢
    cases L with
    | nil => cases hb
    | cons x l =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      rw [List.getD_cons_zero, hb]
  have hsteps := trioSteps_tTabs hO OctC.length OctC.items OctC.base hT TrioC.length
    (T12C.tB_eq ▸ T12C.close_ok) T12C.idx0_ok
  unfold Native.trio12Check
  rw [genFixCheck_of hS SextC.length T12C.b7_ok T12C.b7_asc T12C.b7_lt
      (T12C.tB_eq ▸ T12C.genFix_ok),
    baseSextCheck_of hS SextC.length SextC.items T12C.base_ok,
    trioOrbitCheck_of hT TrioC.length hsteps (piSteps_closed TrioC.length T12C.close_ok) h0T
      T12C.orb_ok,
    tupOrbitCheck_of hO OctC.length hS SextC.length SextC.items (T12C.lB_eq ▸ T12C.tup_ok)]
  rfl

end CertificateChecks.Batch89018

namespace Certificates

open CertificateChecks

theorem certificate89018 : CFSG.Quasithin.H13.AS91.M24G.Native.trio12Check () = true :=
  CertificateChecks.Batch89018.check_holds

end Certificates

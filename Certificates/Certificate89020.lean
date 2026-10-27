module

public import Certificates.Data.CFSGNative.AS91.M24TrioOne
import CFSG.Certificates.Kernel.M24G.TrioOneSound
import CFSG.Certificates.Kernel.M24G.ReplayFacts
import Certificates.Kernel.M24G.ListsEq
import Certificates.Kernel.M24G.TrioChecks
import Certificates.Kernel.M24G.SextChecks
import Certificates.Kernel.M24G.TrioOneChecks
import Certificates.Kernel.M24G.TrioOneGroup

public section

namespace Certificates

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem certificate89020 : CFSG.Quasithin.H13.AS91.M24G.Native.r121Check () = true := by
  have h0 : TL.getD 0 default = Native.baseTrio := by
    have hb := (replay_facts trioReplay_ok).2.1
    generalize TL = L at hb ⊢
    cases L with
    | nil => cases hb
    | cons x l =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      rw [List.getD_cons_zero, hb]
  unfold Native.r121Check
  rw [groupCheck_of groupL_ok,
    fixCopCheck_of groupL_ok trioList_eq sextList_eq TrioC.length SextC.length h0 fixCopW_ok]
  rfl

end Certificates

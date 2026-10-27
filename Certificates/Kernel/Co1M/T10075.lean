
module

public import Certificates.Kernel.Co1M.K10075
public import Certificates.Kernel.Co1M.W10070
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.InvFam CFSG.KC.SortTree CFSG.Sporadic.Co1.Module

theorem t3a : chunksK (actV RT75 [0, 1]) 2 u3v75 T3.tab 47104 24 T3.wl T3.wp T3.B 0 184 = true := by
  quickRfl

theorem t3b : chunksK (actV RT75 [0, 1]) 2 u3v75 T3.tab 47104 24 T3.wl T3.wp T3.B 184 184 = true := by
  quickRfl

theorem t3c : chunksK (actV RT75 [0, 1]) 2 u3v75 T3.tab 47104 24 T3.wl T3.wp T3.B 368 184 = true := by
  quickRfl

theorem t3d : chunksK (actV RT75 [0, 1]) 2 u3v75 T3.tab 47104 24 T3.wl T3.wp T3.B 552 184 = true := by
  quickRfl

theorem t4a : chunksK (actV RT75 [0, 1]) 2 3 T4.tab 46575 24 T4.wl T4.wp T4.B 0 182 = true := by
  quickRfl

theorem t4b : chunksK (actV RT75 [0, 1]) 2 3 T4.tab 46575 24 T4.wl T4.wp T4.B 182 182 = true := by
  quickRfl

theorem t4c : chunksK (actV RT75 [0, 1]) 2 3 T4.tab 46575 24 T4.wl T4.wp T4.B 364 182 = true := by
  quickRfl

theorem t4d : chunksK (actV RT75 [0, 1]) 2 3 T4.tab 46575 24 T4.wl T4.wp T4.B 546 182 = true := by
  quickRfl

theorem tree4 {act : Nat → Nat → Nat} {ng root n : Nat} {T : STree} {k : Nat} (hC : T.C = 4 * k)
    (hcov : n ≤ T.C * T.B)
    (ha : chunksK act ng root T.tab n 24 T.wl T.wp T.B 0 k = true)
    (hb : chunksK act ng root T.tab n 24 T.wl T.wp T.B k k = true)
    (hc : chunksK act ng root T.tab n 24 T.wl T.wp T.B (2 * k) k = true)
    (hd : chunksK act ng root T.tab n 24 T.wl T.wp T.B (3 * k) k = true) :
    T.OK act ng root 24 n := by
  refine ⟨hcov, fun c hc' => ?_⟩
  rw [hC] at hc'
  by_cases h1 : c < k
  · simpa using chunks_spec ha c h1
  · by_cases h2 : c < 2 * k
    · have := chunks_spec hb (c - k) (by omega)
      rwa [Nat.add_sub_cancel' (by omega)] at this
    · by_cases h3 : c < 3 * k
      · have := chunks_spec hc (c - 2 * k) (by omega)
        rwa [Nat.add_sub_cancel' (by omega)] at this
      · have := chunks_spec hd (c - 3 * k) (by omega)
        rwa [Nat.add_sub_cancel' (by omega)] at this

theorem T3_ok : T3.OK (actV RT75 [0, 1]) 2 u3v75 24 47104 :=
  tree4 (k := 184) rfl (by decide) t3a t3b t3c t3d

theorem T4_ok : T4.OK (actV RT75 [0, 1]) 2 3 24 46575 :=
  tree4 (k := 182) rfl (by decide) t4a t4b t4c t4d

end CertificateChecks.KernelCo1M

end

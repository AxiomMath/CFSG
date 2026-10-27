module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P516Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtB

public section

namespace CFSG.Quasithin.Fan86

namespace P516

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem gcirc_comm (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28)
    (hΞ : ∀ T : Track Γ G, ¬ Xi 1 T) (h515b : Fan515b F) (T : Track Γ G) {z z' : G}
    {a tL tR a' b' tL' tR' : ℤ} (hT : InXi T) (hz : z ∈ T.line.ZZ) (hz1 : z ≠ 1)
    (hc : T.line.IsCoreFix z a (a + 2) tL tR) (hz' : z' ∈ T.line.ZZ)
    (hp : T.line.InPos z z' a (a + 2) tL tR a' b' tL' tR')
    (hval : valence Γ (T.line.vert (a + 1)) ≠ 3) (hr : 5 ≤ tR - (a + 2))
    (hu1 : fcomm z z' ≠ 1) (hf4 : fcomm z z' • T.line.vert (a + 4) = T.line.vert (a + 4))
    (hf5 : fcomm z z' • T.line.vert (a + 5) = T.line.vert (a + 5)) {y : G}
    (hy5 : y • T.line.vert (a + 5) = T.line.vert (a + 5))
    (hy4 : y • T.line.vert (a + 4) ≠ T.line.vert (a + 4))
    (hyu : y * fcomm z z' = fcomm z z' * y) :
    ∀ g ∈ Arc.GcircL G (T.line.arc (a + 3) 2), g * fcomm z z' = fcomm z z' * g := by
  have hadj : Γ.Adj (T.line.vert (a + 4)) (T.line.vert (a + 5)) := by
    have := T.line.adj (a + 4)
    rwa [show a + 4 + 1 = a + 5 by ring] at this
  have e4 : a + 1 + ((3 : ℕ) : ℤ) = a + 4 := by push_cast; ring
  have hC : ∀ g : G, g * fcomm z z' = fcomm z z' * g →
      g ∈ MulAction.stabilizer G (T.line.vert (a + 1 + ((3 : ℕ) : ℤ))) →
        g ∈ MulAction.stabilizer G (T.line.vert (a + 1 + ((3 : ℕ) : ℤ) + 1)) := by
    intro g hgu hg4
    by_contra hg5
    rw [e4] at hg4
    rw [e4, show a + 4 + 1 = a + 5 by ring] at hg5
    exact not_cross F h40 h28 hΞ hadj hu1 hf4 hf5 (MulAction.mem_stabilizer_iff.1 hg4)
      (fun h => hg5 (MulAction.mem_stabilizer_iff.2 h)) hy5 hy4 hgu hyu
  exact h515b h40 T z z' a tL tR a' b' tL' tR' hT hz hz1 hc hz' hp hval hr 3 le_rfl hC
    (lineNSR_of_fan40 h40 T.line (k := 3) (by norm_num) (by norm_num) (a + 1))

end P516

end CFSG.Quasithin.Fan86

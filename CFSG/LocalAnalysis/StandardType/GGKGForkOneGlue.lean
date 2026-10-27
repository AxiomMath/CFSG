module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGRealKGUNonsplitRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRealRootLabel_of_fork {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hl : GGForkRootSL2Label p lab) : GGRealRootLabel p lab := by
  obtain ⟨hp5, hs⟩ := hl
  have hd := ggKG_dvd_of_split hp5 hs
  have hn : 1 ≤ lab.n := hlab.1
  have h2 : 2 ≤ lab.n := by
    by_contra h
    have h1 : lab.n = 1 := by omega
    rw [h1] at hd
    rcases hd with hd | hd <;> have := Nat.le_of_dvd (by norm_num) hd <;> omega
  refine ⟨by omega, h2, ?_⟩
  have h1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
  have h4 : 4 ^ lab.n = 2 ^ lab.n * 2 ^ lab.n := by rw [← mul_pow]; norm_num
  have hprod : (2 ^ lab.n - 1) * (2 ^ lab.n + 1) = 4 ^ lab.n - 1 := by
    rw [h4]
    zify [h1, Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ lab.n * 2 ^ lab.n ≠ 0)]
    ring
  rw [← hprod]
  rcases hd with hd | hd
  · exact hd.mul_right _
  · exact hd.mul_left _

theorem ggKGOneOn_of_realRootSL2On {S S' : ℕ → LargeEvenLabel → Prop} (h : GGRealRootSL2On S')
    (hS : ∀ p lab, GGForkRootSL2Label p lab → S p lab → S' p lab) : GGKGOneOn S :=
  fun p lab hp hlab hl hs => h p lab hp hlab (ggRealRootLabel_of_fork hlab hl) (hS p lab hl hs)

theorem ggKGOneOn_twdNonsplit :
    GGKGOneOn (GGKGRowLabel .twdNonsplit) :=
  ggKGOneOn_of_realRootSL2On ggRealRootSL2On_twdNonsplit fun _ _ hl hs => ⟨hl.1, hs⟩

end CFSG.StandardType

end

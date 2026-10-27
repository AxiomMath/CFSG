module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan58aT (F : FanTree Γ G) (h53a : Fan53a F) (h53b : Fan53b F) (h54 : Fan54 F)
    (h51a : Fan51a F) : Fan58aT F := by
  intro h40 T z z' a b tL tR a' b' tL' tR' hz hz' hd hd' hpos hr hl
  obtain ⟨hleft, hright, i, j, hi, hj, h1, h2⟩ := hpos
  obtain ⟨hc1, hc2⟩ :=
    P58.fan58_core F h53a h53b h54 h51a h40 T.line hz hz' hd hd' hi hj h1 h2 hr hl
  refine ⟨?_, ?_⟩
  · rcases hc1 with h | ⟨hi0, hj0⟩
    · exact Or.inl h
    · exact Or.inr ⟨hleft, hright, by omega, by omega⟩
  · rintro ⟨h, hpp⟩
    exact hc2 ⟨h, by have := hpp.pos_left; have := hpp.pos_right; omega,
      by have := hpp.pos_left; have := hpp.pos_right; omega⟩

theorem fan58b (F : FanTree Γ G) (h53a : Fan53a F) (h53b : Fan53b F) (h53c : Fan53c F)
    (h54 : Fan54 F) (h51a : Fan51a F) : Fan58b F := by
  intro h40 T z a b tL tR hz hd hr hl
  have hZ : z ∈ T.line.Zc := P55.zz_le_zc hz
  have hcC : T.line.IsCoreC z a b := h53b h40 T.line z a b hz hd.core
  have hdC : T.line.IsCoreCFix z a b tL tR := ⟨hd.fix, hcC⟩
  have hb2 : b - a ≤ 2 := h53c h40 T.line z a b hZ hcC
  have hab := P55.fix_a_lt hd
  have hr1 : 1 ≤ tR - b := (h53a h40 T.line z a b tL tR hz hd).1
  have hl1 : 1 ≤ a - tL := (h53a h40 T.line z a b tL tR hz hd).2.1
  obtain ⟨m, hpos⟩ := fan55a F h54 h40 T z z a b tL tR a b tL tR hZ hZ hdC hdC
  obtain ⟨-, -, i, j, hi, hj, h1, h2⟩ := hpos
  have hz' : T.τ ^ m * z * T.τ ^ (-m) ∈ T.line.ZZ := by
    rw [zpow_neg]
    exact P55.IsShift.zz (P55.isShift_zpow T m) hz
  have hd' : T.line.IsCoreFix (T.τ ^ m * z * T.τ ^ (-m)) (a + 2 * m) (b + 2 * m) (tL + 2 * m)
      (tR + 2 * m) := by
    rw [zpow_neg]
    exact P55.IsShift.isCoreFix (P55.isShift_zpow T m) hd
  obtain ⟨hc1, hc2⟩ := P58.fan58_core F h53a h53b h54 h51a h40 T.line hz hz' hd hd' hi hj h1 h2
    hr (by omega)
  omega

end CFSG.Quasithin.Fan86

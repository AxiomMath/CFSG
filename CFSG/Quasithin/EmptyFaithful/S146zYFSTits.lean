module

public import CFSG.Quasithin.EmptyFaithful.S146zYFSBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Blueprint CFSG.QuasithinUnique.Setup.X6

theorem facts134Five_tits :
    NoE25Config fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1 := by
  rintro A _ _ L P T hmod hcfg
  obtain ⟨S, Y, k, hS, hSY, hSk, hYk⟩ := E25Config.exists_sylow_le hcfg
  obtain ⟨H, N, hS2, hSH, hSN, hH, hN, hlat, -, -⟩ := titsSylowOvergroupLattice (↥L) hmod S hS
  have hY : Nat.card Y = 51200 := by rw [hYk, ← hSk, hS2]
  rcases hlat Y hSY with h | h | h | h
  · rw [h, hS2] at hY
    omega
  · rw [h, hH] at hY
    omega
  · rw [h, hN] at hY
    omega
  · have hd := Subgroup.card_dvd_of_le (h ▸ le_top : N ≤ Y)
    rw [hN, hY] at hd
    omega

end CFSG.Quasithin.S146zY

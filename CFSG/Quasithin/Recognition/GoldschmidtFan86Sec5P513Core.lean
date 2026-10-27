module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Rank48
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem track_fixer_eq_bot (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28)
    (hΞ : ∀ T : Track Γ G, ¬ Xi 1 T) (T : Track Γ G) : T.fixer = ⊥ := by
  by_contra h
  obtain ⟨T', -, hT'⟩ := fan48_1 F h40 h28 T h
  exact hΞ T' hT'

theorem fixes_track_of_commute (T : Track Γ G) {z : G} (hτ : T.τ * z = z * T.τ) {k : ℤ}
    (h0 : z • T.line.vert k = T.line.vert k)
    (h1 : z • T.line.vert (k + 1) = T.line.vert (k + 1)) :
    ∀ j : ℤ, z • T.line.vert j = T.line.vert j := by
  have hc : Commute z T.τ := hτ.symm
  have key : ∀ (m i : ℤ), z • T.line.vert i = T.line.vert i →
      z • T.line.vert (i + 2 * m) = T.line.vert (i + 2 * m) := by
    intro m i hi
    rw [← T.zpow_smul_vert m i, smul_smul, (hc.zpow_right m).eq, mul_smul, hi]
  intro j
  obtain ⟨m, hm | hm⟩ : ∃ m : ℤ, j = k + 2 * m ∨ j = k + 1 + 2 * m := ⟨(j - k) / 2, by omega⟩
  · rw [hm]
    exact key m k h0
  · rw [hm]
    exact key m (k + 1) h1

theorem no_fixed_cross (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28)
    (hΞ : ∀ T : Track Γ G, ¬ Xi 1 T) {α β : V} (hαβ : Γ.Adj α β) {x y z : G}
    (hc : CrossPair α β x y) (hz1 : z ≠ 1) (hzα : z • α = α) (hzβ : z • β = β)
    (hx : x * z = z * x) (hy : y * z = z * y) : False := by
  have hτ : (trackOfPair F.adj_smul hαβ hc).τ * z = z * (trackOfPair F.adj_smul hαβ hc).τ := by
    rw [trackOfPair_τ, mul_assoc, hx, ← mul_assoc, hy, mul_assoc]
  have h1 : z • (trackOfPair F.adj_smul hαβ hc).line.vert 1 =
      (trackOfPair F.adj_smul hαβ hc).line.vert 1 := by
    rw [trackOfPair_vert_one]
    exact hzα
  have h2 : z • (trackOfPair F.adj_smul hαβ hc).line.vert (1 + 1) =
      (trackOfPair F.adj_smul hαβ hc).line.vert (1 + 1) := by
    rw [show (1 : ℤ) + 1 = 2 by norm_num, trackOfPair_vert_two]
    exact hzβ
  have hmem : z ∈ (trackOfPair F.adj_smul hαβ hc).fixer :=
    ((trackOfPair F.adj_smul hαβ hc).mem_fixer).2 (fixes_track_of_commute _ hτ h1 h2)
  rw [track_fixer_eq_bot F h40 h28 hΞ] at hmem
  exact hz1 (Subgroup.mem_bot.1 hmem)

end CFSG.Quasithin.Fan86

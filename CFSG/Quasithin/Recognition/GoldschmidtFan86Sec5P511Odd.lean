module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P511Conj

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_hasReflections_of_odd (F : FanTree Γ G) (T : Track Γ G) {z : G} (hzz : z * z = 1)
    {tL tR : ℤ} (hfix : ∀ i, i ∈ T.line.fixIdx z ↔ tL ≤ i ∧ i ≤ tR)
    (hLR : tL ≤ tR) (hodd : (tR - tL) % 2 = 1) : ∃ T' : Track Γ G, T'.HasReflections := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, 2 * m = tR - tL + 1 := ⟨(tR - tL + 1) / 2, by omega⟩
  have hv : ∀ i, T.τ ^ m • T.line.vert i = T.line.vert (i + 2 * m) := fun i =>
    T.zpow_smul_vert m i
  set z' := T.τ ^ m * z * (T.τ ^ m)⁻¹ with hz'
  have hz'z' : z' * z' = 1 := by
    calc z' * z' = T.τ ^ m * (z * z) * (T.τ ^ m)⁻¹ := by rw [hz']; group
      _ = 1 := by rw [hzz]; group
  have hcf : ∀ i, i + 2 * m ∈ T.line.fixIdx z' ↔ i ∈ T.line.fixIdx z := fun i =>
    T.line.conj_fix (σ := fun i => i + 2 * m) hv i
  have hzα : z • T.line.vert tR = T.line.vert tR := (hfix tR).2 ⟨hLR, le_rfl⟩
  have hzβ : z • T.line.vert (tR + 1) ≠ T.line.vert (tR + 1) := fun h => by
    have := ((hfix (tR + 1)).1 h).2
    omega
  have hz'β : z' • T.line.vert (tR + 1) = T.line.vert (tR + 1) := by
    have := (hcf tL).2 ((hfix tL).2 ⟨le_rfl, hLR⟩)
    rwa [show tL + 2 * m = tR + 1 by omega] at this
  have hz'α : z' • T.line.vert tR ≠ T.line.vert tR := fun h => by
    have h2 : tR - 2 * m + 2 * m ∈ T.line.fixIdx z' := by
      rw [sub_add_cancel]
      exact h
    have := ((hfix _).1 ((hcf (tR - 2 * m)).1 h2)).1
    omega
  have hcross : CrossPair (T.line.vert tR) (T.line.vert (tR + 1)) z z' :=
    ⟨hzα, hzβ, hz'β, hz'α⟩
  have hαβ : Γ.Adj (T.line.vert tR) (T.line.vert (tR + 1)) := T.line.adj tR
  refine ⟨trackOfPair F.adj_smul hαβ hcross, ?_⟩
  exact (trackOfPair F.adj_smul hαβ hcross).hasReflections_of_two
    ⟨z, trackOfPair_reflection_x F.adj_smul hαβ hcross hzz hz'z'⟩
    ⟨z', trackOfPair_reflection_y F.adj_smul hαβ hcross hzz hz'z'⟩

end CFSG.Quasithin.Fan86

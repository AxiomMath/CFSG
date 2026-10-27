module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63Core

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem track_moves (F : FanTree Γ G) (h40 : Fan40 F) (h62 : Fan62 F) {T : Track Γ G}
    (hT : InXi T) {c : ℤ} {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hcen : z ∈ Cen (T.line.edgeStab (G := G) c : Set G)) :
    ∃ i : ℤ, z • T.line.vert i ≠ T.line.vert i ∧ Γ.dist (T.line.vert c) (T.line.vert i) ≤ 5 := by
  have hZZ : z ∈ T.line.ZZ := ⟨hz2, c, hcen⟩
  obtain ⟨⟨a₀, b₀, tL, tR, hfx⟩, hall⟩ := h62 h40 T hT z hZZ hz1
  have hP : ∀ k, z ∈ Cen (T.line.edgeStab (G := G) k : Set G) →
      k ∈ T.line.fixIdx z ∧ k + 1 ∈ T.line.fixIdx z := fun k hk =>
    ⟨MulAction.mem_stabilizer_iff.1 hk.1.1, MulAction.mem_stabilizer_iff.1 hk.1.2⟩
  obtain ⟨a, b, hac, hcb, hcore⟩ := P63.exists_core_run T.line (P := fun i => z ∈ Cen
    (T.line.edgeStab (G := G) i : Set G)) hfx.fix hP hcen
  have hcf : T.line.IsCoreFix z a b tL tR := ⟨hfx.fix, hcore⟩
  obtain ⟨hba, hrb, hal⟩ := hall a b tL tR hcf
  refine ⟨a - 4, fun hfix => ?_, ?_⟩
  · have := (hfx.fix (a - 4)).1 hfix
    omega
  · rw [SimpleGraph.dist_comm, Line.dist_eq F.isTree T.line (show a - 4 ≤ c by omega)]
    omega

theorem exists_track_edge (F : FanTree Γ G) (T : Track Γ G) :
    ∃ c : ℤ, valence Γ (T.line.vert c) = 5 := by
  by_cases h0 : valence Γ (T.line.vert 0) = 5
  · exact ⟨0, h0⟩
  · refine ⟨1, ?_⟩
    have h1 : valence Γ (T.line.vert 0) ≠ valence Γ (T.line.vert 1) :=
      F.alternating _ _ (by simpa using T.line.adj 0)
    have h2 : valence Γ (T.line.vert 1) = 3 ∨ valence Γ (T.line.vert 1) = 5 := F.valence _
    have h3 : valence Γ (T.line.vert 0) = 3 ∨ valence Γ (T.line.vert 0) = 5 := F.valence _
    omega

end P74

end CFSG.Quasithin.Fan86

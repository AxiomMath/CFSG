module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_move_next {n i : ℕ} {P : Arc Γ n} (hi1 : 1 ≤ i) (hin : i < n)
    (hnR : ¬ RightSingular Γ G P.vert 0 i) :
    ∃ x ∈ stabRange G P.vert 0 i, x • P.vert (i + 1) ≠ P.vert (i + 1) := by
  by_contra hcon
  push Not at hcon
  refine hnR ⟨P.vert (i + 1), P.adj i hin, ?_, hcon⟩
  have h := P.nb (i - 1) (by omega)
  rw [show i - 1 + 2 = i + 1 by omega] at h
  exact h.symm

theorem exists_move_prev {n i : ℕ} {P : Arc Γ n} (hin : i + 1 < n)
    (hnL : ¬ LeftSingular Γ G P.vert (i + 1) n) :
    ∃ y ∈ stabRange G P.vert (i + 1) n, y • P.vert i ≠ P.vert i := by
  by_contra hcon
  push Not at hcon
  refine hnL ⟨P.vert i, (P.adj i (by omega)).symm, ?_, hcon⟩
  exact P.nb i (by omega)

theorem fan513a (F : FanTree Γ G) (h28 : Fan28) : Fan513a F := by
  intro h40 hΞ n i P hi1 hi2 hnR hnL z hz₀ z₁ hz₁ hz
  subst hz
  obtain ⟨hz1, -, hzs0, hzc0⟩ := hz₀
  obtain ⟨-, -, hzs2, hzc2⟩ := hz₁
  have hz0 : z • P.vert 0 = P.vert 0 := MulAction.mem_stabilizer_iff.1 hzs0
  have hz2 : z • P.vert (2 * n) = P.vert (2 * n) := MulAction.mem_stabilizer_iff.1 hzs2
  have hall : ∀ k, k ≤ 2 * n → z • P.vert k = P.vert k := fun k hk =>
    Arc.fixes_of_ends F.isTree F.adj_smul P hz0 hz2 k hk
  obtain ⟨x, hxS, hxmove⟩ := exists_move_next hi1 (by omega) hnR
  have hxmem : x ∈ MulAction.stabilizer G (P.vert 0) :=
    MulAction.mem_stabilizer_iff.2 (mem_stabRange.1 hxS 0 le_rfl (Nat.zero_le _))
  have hy : ∃ y : G, y • P.vert (i + 1) = P.vert (i + 1) ∧ y • P.vert (2 * n) = P.vert (2 * n) ∧
      y • P.vert i ≠ P.vert i := by
    by_cases hlt : i + 1 < 2 * n
    · obtain ⟨y, hyS, hymove⟩ := exists_move_prev hlt (hnL hlt)
      exact ⟨y, mem_stabRange.1 hyS (i + 1) le_rfl (by omega),
        mem_stabRange.1 hyS (2 * n) (by omega) le_rfl, hymove⟩
    · have hin : i + 1 = 2 * n := by omega
      have hadj : Γ.Adj (P.vert (2 * n)) (P.vert i) := by
        have h := (P.adj i (by omega)).symm
        rwa [hin] at h
      obtain ⟨γ, hγ, hγne⟩ := F.exists_adj_ne (P.vert (2 * n)) (P.vert i)
      obtain ⟨y, hyS, hyγ⟩ := F.loc_trans (P.vert (2 * n)) (P.vert i) γ hadj hγ
      have hy2 : y • P.vert (2 * n) = P.vert (2 * n) := MulAction.mem_stabilizer_iff.1 hyS
      refine ⟨y, by rw [hin]; exact hy2, hy2, ?_⟩
      rw [hyγ]
      exact hγne
  obtain ⟨y, hy1, hy2, hymove⟩ := hy
  have hymem : y ∈ MulAction.stabilizer G (P.vert (2 * n)) := MulAction.mem_stabilizer_iff.2 hy2
  have hcross : CrossPair (P.vert i) (P.vert (i + 1)) x y :=
    ⟨mem_stabRange.1 hxS i (Nat.zero_le _) le_rfl, hxmove, hy1, hymove⟩
  exact no_fixed_cross F h40 h28 hΞ (P.adj i (by omega)) hcross hz1 (hall i (by omega))
    (hall (i + 1) (by omega)) (hzc0 x hxmem) (hzc2 y hymem)

end CFSG.Quasithin.Fan86

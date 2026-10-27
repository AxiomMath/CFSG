module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Ball
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace P73

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem relIndex_stabilizer_le (H : Subgroup G) (w : V) (T : Set V) (hT : T.Finite)
    (hmem : ∀ h ∈ H, h • w ∈ T) :
    (MulAction.stabilizer G w).relIndex H ≤ T.ncard ∧
      (MulAction.stabilizer G w).relIndex H ≠ 0 := by
  have h1 : (MulAction.stabilizer G w).relIndex H = (MulAction.orbit H w).ncard := by
    rw [← MulAction.index_stabilizer]
    have : MulAction.stabilizer H w = (MulAction.stabilizer G w).subgroupOf H := by
      ext g
      simp [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    rw [this]
    rfl
  have hsub : MulAction.orbit H w ⊆ T := by
    rintro _ ⟨g, rfl⟩
    exact hmem g g.2
  rw [h1]
  refine ⟨Set.ncard_le_ncard hsub hT, ?_⟩
  have hfin : (MulAction.orbit H w).Finite := hT.subset hsub
  have : 0 < (MulAction.orbit H w).ncard :=
    (Set.ncard_pos hfin).2 ⟨w, MulAction.mem_orbit_self w⟩
  omega

theorem step_le (F : FanTree Γ G) {H : Subgroup G} {c u w : V} {k : ℕ} (hc : valence Γ c = k)
    (hcu : Γ.Adj c u) (hcw : Γ.Adj c w) (hwu : w ≠ u) (hHc : ∀ h ∈ H, h • c = c)
    (hHu : ∀ h ∈ H, h • u = u) :
    (MulAction.stabilizer G w).relIndex H ≤ k - 1 ∧
      (MulAction.stabilizer G w).relIndex H ≠ 0 := by
  have hk : 0 < k := by
    have h := F.valence c
    have hc' : Nat.card (Γ.neighborSet c) = k := hc
    omega
  have hfin : (Γ.neighborSet c \ {u}).Finite :=
    (neighborSet_finite hk hc).subset Set.sdiff_subset
  have hncard := neighborSet_diff_ncard hc hcu
  have := relIndex_stabilizer_le H w (Γ.neighborSet c \ {u}) hfin (fun h hh => by
    refine ⟨?_, ?_⟩
    · have := (F.adj_smul h c w).2 hcw
      rwa [hHc h hh] at this
    · intro e
      rw [Set.mem_singleton_iff] at e
      exact hwu (MulAction.injective h (e.trans (hHu h hh).symm)))
  rw [hncard] at this
  exact this

theorem ball_fix (F : FanTree Γ G) {α : V} (P : Arc Γ 8) (h4 : P.vert 4 = α) {g : G}
    (hg : g ∈ ballStab Γ G 2 α) :
    g • P.vert 2 = P.vert 2 ∧ g • P.vert 3 = P.vert 3 ∧ g • P.vert 5 = P.vert 5 ∧
      g • P.vert 6 = P.vert 6 := by
  obtain ⟨hg1, hg2⟩ := (F.mem_ballStab_two_iff).1 hg
  have a3 : Γ.Adj α (P.vert 3) := by
    rw [← h4]
    exact (P.adj 3 (by norm_num)).symm
  have a5 : Γ.Adj α (P.vert 5) := by
    rw [← h4]
    exact P.adj 4 (by norm_num)
  have a32 : Γ.Adj (P.vert 3) (P.vert 2) := (P.adj 2 (by norm_num)).symm
  have a56 : Γ.Adj (P.vert 5) (P.vert 6) := P.adj 5 (by norm_num)
  exact ⟨mem_nbrStab.1 (hg2 _ a3) _ a32, mem_nbrStab.1 hg1 _ a3, mem_nbrStab.1 hg1 _ a5,
    mem_nbrStab.1 (hg2 _ a5) _ a56⟩

theorem stab_relIndex_le (F : FanTree Γ G) {α : V} (hα : valence Γ α = 5) (P : Arc Γ 8)
    (h4 : P.vert 4 = α) : (P.stab G).relIndex (ballStab Γ G 2 α) ≤ 64 := by
  have v4 : valence Γ (P.vert 4) = 5 := by rw [h4]; exact hα
  have v3 : valence Γ (P.vert 3) = 3 := valence_adj_three F v4 (P.adj 3 (by norm_num)).symm
  have v2 : valence Γ (P.vert 2) = 5 := valence_adj_five F v3 (P.adj 2 (by norm_num)).symm
  have v1 : valence Γ (P.vert 1) = 3 := valence_adj_three F v2 (P.adj 1 (by norm_num)).symm
  have v5 : valence Γ (P.vert 5) = 3 := valence_adj_three F v4 (P.adj 4 (by norm_num))
  have v6 : valence Γ (P.vert 6) = 5 := valence_adj_five F v5 (P.adj 5 (by norm_num))
  have v7 : valence Γ (P.vert 7) = 3 := valence_adj_three F v6 (P.adj 6 (by norm_num))
  set B := ballStab Γ G 2 α with hB
  have hfix := fun g (hg : g ∈ B) => ball_fix F P h4 hg
  set S1 := MulAction.stabilizer G (P.vert 1) ⊓ B with hS1
  set S2 := MulAction.stabilizer G (P.vert 0) ⊓ S1 with hS2
  set S3 := MulAction.stabilizer G (P.vert 7) ⊓ S2 with hS3
  set S4 := MulAction.stabilizer G (P.vert 8) ⊓ S3 with hS4
  have s21 : S2 ≤ S1 := inf_le_right
  have s32 : S3 ≤ S2 := inf_le_right
  have s43 : S4 ≤ S3 := inf_le_right
  have s1B : S1 ≤ B := inf_le_right
  have hS1B : ∀ g ∈ S1, g ∈ B := fun g hg => hg.2
  have hS2B : ∀ g ∈ S2, g ∈ B := fun g hg => hg.2.2
  have hS3B : ∀ g ∈ S3, g ∈ B := fun g hg => hg.2.2.2
  have b1 : S1.relIndex B ≤ 4 ∧ S1.relIndex B ≠ 0 := by
    have := step_le F (H := B) v2 (P.adj 2 (by norm_num)) (P.adj 1 (by norm_num)).symm
      (P.nb 1 (by norm_num)) (fun h hh => (hfix h hh).1) (fun h hh => (hfix h hh).2.1)
    rw [hS1, Subgroup.inf_relIndex_right]
    exact ⟨this.1, this.2⟩
  have b2 : S2.relIndex S1 ≤ 2 ∧ S2.relIndex S1 ≠ 0 := by
    have := step_le F (H := S1) v1 (P.adj 1 (by norm_num)) (P.adj 0 (by norm_num)).symm
      (P.nb 0 (by norm_num)) (fun h hh => MulAction.mem_stabilizer_iff.1 hh.1)
      (fun h hh => (hfix h hh.2).1)
    rw [hS2, Subgroup.inf_relIndex_right]
    exact ⟨this.1, this.2⟩
  have b3 : S3.relIndex S2 ≤ 4 ∧ S3.relIndex S2 ≠ 0 := by
    have := step_le F (H := S2) v6 (P.adj 5 (by norm_num)).symm (P.adj 6 (by norm_num))
      (fun e => P.nb 5 (by norm_num) e.symm) (fun h hh => (hfix h (hS2B h hh)).2.2.2)
      (fun h hh => (hfix h (hS2B h hh)).2.2.1)
    rw [hS3, Subgroup.inf_relIndex_right]
    exact ⟨this.1, this.2⟩
  have b4 : S4.relIndex S3 ≤ 2 ∧ S4.relIndex S3 ≠ 0 := by
    have := step_le F (H := S3) v7 (P.adj 6 (by norm_num)).symm (P.adj 7 (by norm_num))
      (fun e => P.nb 6 (by norm_num) e.symm) (fun h hh => MulAction.mem_stabilizer_iff.1 hh.1)
      (fun h hh => (hfix h (hS3B h hh)).2.2.2)
    rw [hS4, Subgroup.inf_relIndex_right]
    exact ⟨this.1, this.2⟩
  have e1 := Subgroup.relIndex_mul_relIndex S4 S3 S2 s43 s32
  have e2 := Subgroup.relIndex_mul_relIndex S4 S2 S1 (s43.trans s32) s21
  have e3 := Subgroup.relIndex_mul_relIndex S4 S1 B ((s43.trans s32).trans s21) s1B
  have hnz : S4.relIndex B ≠ 0 := by
    rw [← e3, ← e2, ← e1]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero b4.2 b3.2) b2.2) b1.2
  have hle : S4 ≤ P.stab G := by
    intro g hg
    have hgB := hS3B g hg.2
    obtain ⟨f2, f3, f5, f6⟩ := hfix g hgB
    rw [Arc.mem_stab]
    intro i hi
    have f1 : g • P.vert 1 = P.vert 1 := MulAction.mem_stabilizer_iff.1 hg.2.2.2.1
    have f0 : g • P.vert 0 = P.vert 0 := MulAction.mem_stabilizer_iff.1 hg.2.2.1
    have f7 : g • P.vert 7 = P.vert 7 := MulAction.mem_stabilizer_iff.1 hg.2.1
    have f8 : g • P.vert 8 = P.vert 8 := MulAction.mem_stabilizer_iff.1 hg.1
    have f4 : g • P.vert 4 = P.vert 4 := by
      rw [h4]
      exact MulAction.mem_stabilizer_iff.1
        (F.nbrStab_le_stabilizer α ((F.mem_ballStab_two_iff).1 hgB).1)
    interval_cases i <;> assumption
  have hmain := Subgroup.relIndex_le_of_le_left hle hnz
  have hprod : S4.relIndex B ≤ 64 := by
    rw [← e3, ← e2, ← e1]
    calc S4.relIndex S3 * S3.relIndex S2 * S2.relIndex S1 * S1.relIndex B
        ≤ 2 * 4 * 2 * 4 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul b4.1 b3.1) b2.1) b1.1
      _ = 64 := by norm_num
  exact hmain.trans hprod

end P73

end CFSG.Quasithin.Fan86

module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Lbl

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

open P62

namespace P63

theorem exists_dist_pred (F : FanTree Γ G) {v w : V} {n : ℕ} (h : Γ.dist v w = n + 1) :
    ∃ u, Γ.Adj u w ∧ Γ.dist v u = n := by
  obtain ⟨p, hp⟩ := F.isTree.connected.exists_walk_length_eq_dist v w
  have hq : p.reverse.length = n + 1 := by rw [Walk.length_reverse, hp, h]
  generalize p.reverse = r at hq
  cases r with
  | nil => simp at hq
  | @cons _ u _ hadj q =>
    refine ⟨u, hadj.symm, le_antisymm ?_ ?_⟩
    · have := SimpleGraph.dist_le q.reverse
      simp only [Walk.length_reverse, Walk.length_cons] at this hq
      omega
    · have h1 := F.isTree.connected.dist_triangle (u := v) (v := u) (w := w)
      have h2 : Γ.dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hadj.symm
      omega

theorem neighborSet_eq_three (F : FanTree Γ G) {v a b c : V} (hv : valence Γ v = 3)
    (ha : Γ.Adj v a) (hb : Γ.Adj v b) (hc : Γ.Adj v c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Γ.neighborSet v = {a, b, c} := by
  have hcard : (Γ.neighborSet v).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hv
  have hfin : (Γ.neighborSet v).Finite := (F.ncard_neighborSet_le v).2
  have hsub : ({a, b, c} : Set V) ⊆ Γ.neighborSet v := by
    rintro x (rfl | rfl | rfl) <;> assumption
  symm
  refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
  rw [hcard, Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]

theorem moves_of_fix (F : FanTree Γ G) {v u w : V} {a : G} (ha : a ∈ MulAction.stabilizer G v)
    (hu : Γ.Adj v u) (hw : Γ.Adj v w) (huw : u ≠ w) (hau : a • u = u)
    (haK : a ∉ nbrStab Γ G v) : a • w ≠ w := fun haw =>
  haK fun c hc => F.frobenius_two v u w hu hw huw a ha hau haw c hc

variable {L : ZLab Γ G} (F : FanTree Γ G) (H : LabHyp L)
include F H

theorem ballStab_three {δ : V} (hδ : valence Γ δ = 5) : L.z δ ∈ ballStab Γ G 3 δ := by
  have hK : L.z δ ∈ nbrStab Γ G δ := cinv_mem_nbrStab F (cinv_iff.2 (L.isCentral δ hδ))
  have hl2 : ∀ {l : V}, Γ.dist δ l = 2 → L.z δ ∈ nbrStab Γ G l := by
    intro l hl
    obtain ⟨ν, hν⟩ := exists_br F hl
    have hvl := (Br.valence F hδ hν).2
    exact H.ker l δ hvl (by rw [SimpleGraph.dist_comm]; exact hl)
  refine mem_ballStab.2 fun w hw => ?_
  have hcase : Γ.dist δ w = 0 ∨ Γ.dist δ w = 1 ∨ Γ.dist δ w = 2 ∨ Γ.dist δ w = 3 := by omega
  rcases hcase with h | h | h | h
  · obtain rfl := (F.isTree.connected.dist_eq_zero_iff).1 h
    exact MulAction.mem_stabilizer_iff.1 (L.isCentral δ hδ).1
  · exact mem_nbrStab.1 hK w (SimpleGraph.dist_eq_one_iff_adj.1 h)
  · exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer w (hl2 h))
  · obtain ⟨u, hu, hdu⟩ := exists_dist_pred F (n := 2) h
    exact mem_nbrStab.1 (hl2 hdu) w hu

end P63

end CFSG.Quasithin.Fan86

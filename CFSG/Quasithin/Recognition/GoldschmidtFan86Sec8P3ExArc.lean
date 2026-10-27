module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Arc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_arc_start (hdeg : ∀ u v, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v) {a b : V}
    (hab : Γ.Adj a b) : ∀ n : ℕ, ∃ Q : Arc Γ (n + 1), Q.vert 0 = a ∧ Q.vert 1 = b
  | 0 => ⟨Arc.step a b hab, by simp [Arc.step], by simp [Arc.step]⟩
  | n + 1 => by
    obtain ⟨Q, h0, h1⟩ := exists_arc_start hdeg hab n
    have hadj : Γ.Adj (Q.vert (n + 1)) (Q.vert n) := (Q.adj n (by omega)).symm
    obtain ⟨w, hw, hwne⟩ := hdeg _ _ hadj
    have hj : Q.vert (n + 1) = (Arc.step (Q.vert (n + 1)) w hw).vert 0 := by simp [Arc.step]
    have hnb : 1 ≤ n + 1 → 1 ≤ 1 → Q.vert (n + 1 - 1) ≠ (Arc.step (Q.vert (n + 1)) w hw).vert 1 :=
      fun _ _ => by
        rw [show (Arc.step (Q.vert (n + 1)) w hw).vert 1 = w by simp [Arc.step]]
        exact hwne.symm
    refine ⟨Arc.append Q (Arc.step (Q.vert (n + 1)) w hw) hj hnb, ?_, ?_⟩
    · rw [Arc.append_vert_le _ _ _ _ (Nat.zero_le _), h0]
    · rw [Arc.append_vert_le _ _ _ _ (by omega : 1 ≤ n + 1), h1]

theorem exists_two_arcs (F : FanTree Γ G) (α : V) :
    ∃ Q₁ Q₂ : Arc Γ 4, Q₁.vert 0 = α ∧ Q₂.vert 0 = α ∧ Q₁.vert 1 ≠ Q₂.vert 1 := by
  have hdeg : ∀ u v, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v := fun u v _ => F.exists_adj_ne u v
  obtain ⟨b₁, hb₁⟩ := F.exists_adj α
  obtain ⟨b₂, hb₂, hb₂₁⟩ := F.exists_adj_ne α b₁
  obtain ⟨Q₁, h10, h11⟩ := exists_arc_start hdeg hb₁ 3
  obtain ⟨Q₂, h20, h21⟩ := exists_arc_start hdeg hb₂ 3
  exact ⟨Q₁, Q₂, h10, h20, by rw [h11, h21]; exact hb₂₁.symm⟩

theorem exists_arc_eight {Q₁ Q₂ : Arc Γ 4} (h0 : Q₁.vert 0 = Q₂.vert 0)
    (h1 : Q₁.vert 1 ≠ Q₂.vert 1) :
    ∃ Q : Arc Γ 8, Q.vert 0 = Q₁.vert 4 ∧ Q.vert 4 = Q₁.vert 0 ∧ Q.vert 8 = Q₂.vert 4 := by
  have hj : (Arc.rev Q₁).vert 4 = Q₂.vert 0 := by
    rw [Arc.rev_vert]
    simpa using h0
  have hnb : 1 ≤ 4 → 1 ≤ 4 → (Arc.rev Q₁).vert (4 - 1) ≠ Q₂.vert 1 := fun _ _ => by
    rw [Arc.rev_vert]
    exact h1
  refine ⟨Arc.append (Arc.rev Q₁) Q₂ hj hnb, ?_, ?_, ?_⟩
  · rw [Arc.append_vert_le _ _ _ _ (Nat.zero_le 4), Arc.rev_vert]
  · rw [Arc.append_vert_le _ _ _ _ le_rfl, Arc.rev_vert]
  · rw [Arc.append_vert_ge _ _ _ _ (by norm_num : 4 ≤ 8)]

end CFSG.Quasithin.Fan86

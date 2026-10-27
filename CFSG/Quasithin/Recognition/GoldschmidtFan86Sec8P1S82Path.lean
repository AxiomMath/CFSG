module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem pathSet_start (F : FanTree Γ G) (m : Fin 5) {a : ℕ} (ha : a ≤ 4) :
    pathSet Γ α ((D.P m).vert a) = {v | ∃ n, n ≤ a ∧ v = (D.P m).vert n} := by
  ext v
  have := Arc.mem_pathSet_iff F.isTree (Arc.take (D.P m) a ha) v
  rw [show (Arc.take (D.P m) a ha).vert 0 = α from D.start m] at this
  exact this

theorem pathSet_branches (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 5} (hij : i ≠ j)
    {a b : ℕ} (ha : a ≤ 4) (hb : b ≤ 4) :
    pathSet Γ ((D.P i).vert a) ((D.P j).vert b) =
      {v | (∃ n, n ≤ a ∧ v = (D.P i).vert n) ∨ ∃ n, n ≤ b ∧ v = (D.P j).vert n} := by
  have hbb : (D.P i).vert 1 ≠ (D.P j).vert 1 := fun h' => hij (D.beta_injective F h h')
  have hA : ∀ k, k ≤ a → (Arc.rev (Arc.take (D.P i) a ha)).vert k = (D.P i).vert (a - k) :=
    fun k _ => Arc.rev_vert _ k
  have hjn : (Arc.rev (Arc.take (D.P i) a ha)).vert a = (Arc.take (D.P j) b hb).vert 0 := by
    rw [hA a le_rfl, Nat.sub_self, D.start]
    exact (D.start j).symm
  have hnb : 1 ≤ a → 1 ≤ b →
      (Arc.rev (Arc.take (D.P i) a ha)).vert (a - 1) ≠ (Arc.take (D.P j) b hb).vert 1 :=
    fun h1 h2 => by
      rw [hA (a - 1) (by omega), show a - (a - 1) = 1 by omega]
      exact hbb
  set C := Arc.append (Arc.rev (Arc.take (D.P i) a ha)) (Arc.take (D.P j) b hb) hjn hnb with hC
  have hC0 : C.vert 0 = (D.P i).vert a := by
    rw [hC, Arc.append_vert_le _ _ _ _ (Nat.zero_le a), hA 0 (Nat.zero_le a), Nat.sub_zero]
  have hCn : C.vert (a + b) = (D.P j).vert b := by
    rw [hC, Arc.append_vert_ge _ _ _ _ (Nat.le_add_right a b), Nat.add_sub_cancel_left]
    rfl
  have hle : ∀ k, k ≤ a → C.vert k = (D.P i).vert (a - k) := fun k hk => by
    rw [hC, Arc.append_vert_le _ _ _ _ hk, hA k hk]
  have hge : ∀ n, n ≤ b → C.vert (a + n) = (D.P j).vert n := fun n hn => by
    rw [hC, Arc.append_vert_ge _ _ _ _ (Nat.le_add_right a n), Nat.add_sub_cancel_left]
    rfl
  ext v
  have key := Arc.mem_pathSet_iff F.isTree C v
  rw [hC0, hCn] at key
  rw [key]
  constructor
  · rintro ⟨k, hk, rfl⟩
    by_cases hka : k ≤ a
    · exact Or.inl ⟨a - k, by omega, hle k hka⟩
    · have : k = a + (k - a) := by omega
      exact Or.inr ⟨k - a, by omega, by rw [this, hge (k - a) (by omega)]; simp⟩
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · exact ⟨a - n, by omega, by rw [hle (a - n) (by omega)]; congr 1; omega⟩
    · exact ⟨a + n, by omega, (hge n hn).symm⟩

end D10Set

end CFSG.Quasithin.Fan86

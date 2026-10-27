module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem valence_five_three (F : FanTree Γ G) {u v : V} (huv : Γ.Adj u v)
    (h : Fan86.valence Γ u = 5) : Fan86.valence Γ v = 3 := by
  have h1 := F.alternating u v huv
  have h2 := F.valence v
  have e1 : Fan86.valence Γ u = Nat.card (Γ.neighborSet u) := rfl
  have e2 : Fan86.valence Γ v = Nat.card (Γ.neighborSet v) := rfl
  omega

theorem valence_three_five (F : FanTree Γ G) {u v : V} (huv : Γ.Adj u v)
    (h : Fan86.valence Γ u = 3) : Fan86.valence Γ v = 5 := by
  have h1 := F.alternating u v huv
  have h2 := F.valence v
  have e1 : Fan86.valence Γ u = Nat.card (Γ.neighborSet u) := rfl
  have e2 : Fan86.valence Γ v = Nat.card (Γ.neighborSet v) := rfl
  omega

theorem valence_arc (F : FanTree Γ G) {s : ℕ} (R : Arc Γ s) (h4 : 4 ≤ s)
    (h5 : Fan86.valence Γ (R.vert 4) = 5) (i : ℕ) (hi : i ≤ s) :
    (i % 2 = 0 → Fan86.valence Γ (R.vert i) = 5) ∧
      (i % 2 = 1 → Fan86.valence Γ (R.vert i) = 3) := by
  have step : ∀ j, j < s → ((j % 2 = 0 → Fan86.valence Γ (R.vert j) = 5) ∧
      (j % 2 = 1 → Fan86.valence Γ (R.vert j) = 3)) →
      ((j + 1) % 2 = 0 → Fan86.valence Γ (R.vert (j + 1)) = 5) ∧
      ((j + 1) % 2 = 1 → Fan86.valence Γ (R.vert (j + 1)) = 3) := by
    intro j hj ⟨hA, hB⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact valence_three_five F (R.adj j hj) (hB (by omega))
    · exact valence_five_three F (R.adj j hj) (hA (by omega))
  have back : ∀ j, j < s → ((j + 1) % 2 = 0 → Fan86.valence Γ (R.vert (j + 1)) = 5) ∧
      ((j + 1) % 2 = 1 → Fan86.valence Γ (R.vert (j + 1)) = 3) →
      (j % 2 = 0 → Fan86.valence Γ (R.vert j) = 5) ∧
      (j % 2 = 1 → Fan86.valence Γ (R.vert j) = 3) := by
    intro j hj ⟨hA, hB⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact valence_three_five F (R.adj j hj).symm (hB (by omega))
    · exact valence_five_three F (R.adj j hj).symm (hA (by omega))
  have up : ∀ k, 4 + k ≤ s → ((4 + k) % 2 = 0 → Fan86.valence Γ (R.vert (4 + k)) = 5) ∧
      ((4 + k) % 2 = 1 → Fan86.valence Γ (R.vert (4 + k)) = 3) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun _ => h5, fun h => by omega⟩
    | succ k ih => intro hk; exact step (4 + k) (by omega) (ih (by omega))
  have down : ∀ k, k ≤ 4 → ((4 - k) % 2 = 0 → Fan86.valence Γ (R.vert (4 - k)) = 5) ∧
      ((4 - k) % 2 = 1 → Fan86.valence Γ (R.vert (4 - k)) = 3) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun _ => h5, fun h => by omega⟩
    | succ k ih =>
      intro hk
      have := back (4 - k - 1) (by omega)
        (by rw [show 4 - k - 1 + 1 = 4 - k by omega]; exact ih (by omega))
      rwa [show 4 - (k + 1) = 4 - k - 1 by omega]
  by_cases hi4 : 4 ≤ i
  · have := up (i - 4) (by omega)
    rwa [show 4 + (i - 4) = i by omega] at this
  · have := down (4 - i) (by omega)
    rwa [show 4 - (4 - i) = i by omega] at this

theorem layer_trans {S P : Subgroup G} (hPS : P ≤ S) {v u w : V}
    (h : ∀ y, Γ.Adj v y → y ≠ u → ∃ m ∈ P, m • w = y) :
    ∀ a b, Γ.Adj v a → a ≠ u → Γ.Adj v b → b ≠ u → ∃ g ∈ S, g • a = b := by
  intro a b ha hau hb hbu
  obtain ⟨m, hm, hma⟩ := h a ha hau
  obtain ⟨n, hn, hnb⟩ := h b hb hbu
  refine ⟨n * m⁻¹, S.mul_mem (hPS hn) (S.inv_mem (hPS hm)), ?_⟩
  rw [mul_smul, inv_smul_eq_iff.2 hma.symm, hnb]

theorem finite_nbrStab (F : FanTree Γ G) (v : V) : Finite (nbrStab Γ G v) := by
  have := F.loc_finite v
  exact Finite.of_injective (Subgroup.inclusion (F.nbrStab_le_stabilizer v))
    (Subgroup.inclusion_injective _)

theorem prod_valence_chain (x : ℕ → V) (a : ℕ) (h1 : Fan86.valence Γ (x (a + 1)) = 3)
    (h2 : Fan86.valence Γ (x (a + 2)) = 5) (h3 : Fan86.valence Γ (x (a + 3)) = 3) :
    ∏ j ∈ Finset.range 3, (Fan86.valence Γ (x (a + 1 + j)) - 1) = 16 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, add_zero]
  rw [show a + 1 + 1 = a + 2 by omega, show a + 1 + 2 = a + 3 by omega, h1, h2, h3]
  norm_num

end P71

end CFSG.Quasithin.Fan86

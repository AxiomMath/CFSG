module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltNoFieldOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

theorem A3_char_and_val {p e l f N0 N c : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (he : 1 ≤ e)
    (hc : c = 1 ∨ c = 3)
    (hX : (p ^ e % 3 = 1 ∧ N * c = ordSL (p ^ e)) ∨ (p ^ e % 3 = 2 ∧ N * c = ordSU (p ^ e)))
    (hl : l.Prime) (hY : padicValNat l N = f * N0 ∧ N < l ^ (3 * padicValNat l N)) :
    l = p ∧ f * N0 = 3 * e := by
  have hlp : l = p := by
    by_contra hne
    have hbound : l ^ (3 * padicValNat l N) ≤ N := by
      rcases hX with ⟨hmod, hM⟩ | ⟨hmod, hM⟩
      · exact A1_c_SL hp h5 he hmod hc hM hl hne
      · exact A1_c_SU hp h5 he hmod hc hM hl hne
    exact lt_irrefl _ (lt_of_le_of_lt hbound hY.2)
  refine ⟨hlp, ?_⟩
  rw [← hY.1, hlp]
  rcases hX with ⟨_, hM⟩ | ⟨_, hM⟩
  · exact A1_a_SL hp h5 he hc hM
  · exact A1_a_SU hp h5 he hc hM

theorem A4_core {r M c R : ℕ} (hr : 1 ≤ r) (hc : 1 ≤ c) (hMc : M * c = R)
    (hR : R ≤ (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 3 + 3 * r ^ 2 + 3 * r + 2))
    (hXM : (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3) ≤ 2 * M + 1) :
    False := by
  have hMle : M ≤ M * c := Nat.le_mul_of_pos_right M (by omega)
  have hT0 : 0 < (r + 1) ^ 3 * (r * (r + 2)) :=
    Nat.mul_pos (pow_pos (by omega) 3) (Nat.mul_pos (by omega) (by omega))
  have hT1 : 1 ≤ (r + 1) ^ 3 * (r * (r + 2)) := by omega
  have h2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hPQ : 2 * (r ^ 3 + 3 * r ^ 2 + 3 * r + 2) + 2 ≤ r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3 := by
    nlinarith
  have hkey : (r + 1) ^ 3 * (r * (r + 2)) * (2 * (r ^ 3 + 3 * r ^ 2 + 3 * r + 2) + 2)
      ≤ (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3) :=
    Nat.mul_le_mul (le_refl _) hPQ
  nlinarith

theorem A4_bound {r M : ℕ}
    (hMe : M = (r + 1) ^ 3 * (r * (r + 2) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3)) / 2) :
    (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3) ≤ 2 * M + 1 := by
  rw [mul_assoc, hMe]
  have h1 := Nat.div_add_mod ((r + 1) ^ 3 * (r * (r + 2) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3))) 2
  have h2 := Nat.mod_lt ((r + 1) ^ 3 * (r * (r + 2) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3))) two_pos
  omega

theorem A4_L2_ne_SL {q M c : ℕ} (hq : 5 ≤ q) (hc : c = 1 ∨ c = 3)
    (hM : M * c = ordSL q) : M ≠ q ^ 3 * (q ^ 6 - 1) / 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 1 ≤ r := by omega
  have hc1 : 1 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  have h6 : (r + 1) ^ 6 - 1 = r * (r + 2) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [ordSL_succ] at hM
  intro hMe
  rw [h6] at hMe
  have hR : (r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3))
      ≤ (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 3 + 3 * r ^ 2 + 3 * r + 2) := by
    have e1 : (r + 1) ^ 3 * (r ^ 2 * (r + 2) * (r ^ 2 + 3 * r + 3))
        = (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 3 + 3 * r ^ 2 + 3 * r) := by ring
    rw [e1]
    exact Nat.mul_le_mul (le_refl _) (Nat.le_add_right _ _)
  exact A4_core hr hc1 hM hR (A4_bound hMe)

theorem A4_L2_ne_SU {q M c : ℕ} (hq : 5 ≤ q) (hc : c = 1 ∨ c = 3)
    (hM : M * c = ordSU q) : M ≠ q ^ 3 * (q ^ 6 - 1) / 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 1 ≤ r := by omega
  have hc1 : 1 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  have h6 : (r + 1) ^ 6 - 1 = r * (r + 2) * (r ^ 4 + 4 * r ^ 3 + 7 * r ^ 2 + 6 * r + 3) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [ordSU_succ] at hM
  intro hMe
  rw [h6] at hMe
  have hR : (r + 1) ^ 3 * ((r + 2) ^ 2 * (r * (r ^ 2 + r + 1)))
      ≤ (r + 1) ^ 3 * (r * (r + 2)) * (r ^ 3 + 3 * r ^ 2 + 3 * r + 2) :=
    le_of_eq (by ring)
  exact A4_core hr hc1 hM hR (A4_bound hMe)

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof

end

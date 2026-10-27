module

public import CFSG.Quasithin.Background.Harris.R1.Defs
public import CFSG.Quasithin.Recognition.SzR1FamCenter

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem two_mul_add_le_two_pow (m : ℕ) : 2 * (m + 4) + 6 ≤ 2 ^ (m + 4) := by
  induction m with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

theorem add_two_le_two_pow {n : ℕ} (hn : 2 ≤ n) : n + 2 ≤ 2 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  induction m with
  | zero => norm_num
  | succ k ih => rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]; omega

theorem le_three_of_half_le {n : ℕ} (h : (2 ^ n + 1) / 2 ≤ n + 2) : n ≤ 3 := by
  by_contra hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have := two_mul_add_le_two_pow m
  omega

theorem false_of_half_le {n c : ℕ} (hn : 2 ≤ n) (hc : (2 ^ n) ^ 2 + 1 ≤ c) (h : c / 2 ≤ n + 2) :
    False := by
  have h1 := add_two_le_two_pow hn
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 4 * 2 ^ n ≤ (2 ^ n) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ h4
  omega

theorem nonab_of (h1 : GramAbelStmt) (h2 : AbelIndexStmt) (h3 : FamStmt) (h4 : AutBoundStmt) :
    NonabStmt := by
  intro G _ _ K1 L2 S Zs h hB hna
  obtain ⟨n, hn, hb⟩ := hB
  obtain ⟨Ω, _, C, hodd, hL, hnL⟩ := h3 G K1 L2 S Zs h n hn hb hna
  obtain ⟨A, hAW, hAc, E, hE, hcard⟩ := h2 G K1 L2 S Zs h ⟨n, hn, hb⟩ hna
  have hE4 : Nat.card E ≤ 2 ^ (n + 1) := h4 (OTwoQuot K1) n hn hb E hE
  have h5 : 5 ≤ Fintype.card Ω := by
    have h4n : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    by_cases hl : IsL2Quot n (OTwoQuot K1)
    · rw [hL hl]; omega
    · have := hnL hl
      have : 2 ^ n ≤ (2 ^ n) ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
  obtain ⟨i₀, j₀, hij⟩ : ∃ i₀ j₀ : Ω, i₀ ≠ j₀ :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega) |>.exists_pair_ne
  have hz : C.zU i₀ j₀ ≠ 1 := fun hz => C.cm_ne_one hij (congrArg Subtype.val hz)
  have hG := h1 ↥(vBeta K1 L2 S Zs) Ω (C.zU i₀ j₀) C.wU (C.gramRel hij) hz hodd
    (C.closure_wU hij) (A.subgroupOf (vBeta K1 L2 S Zs))
    (fun a ha b hb => Subtype.ext (hAc _ ha _ hb))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv] at hG
  have hApos : 0 < Nat.card A := Nat.card_pos
  have key : 2 ^ (Fintype.card Ω / 2) ≤ 2 ^ (n + 2) := by
    have : 2 ^ (Fintype.card Ω / 2) * Nat.card A ≤ 2 ^ (n + 2) * Nat.card A :=
      calc 2 ^ (Fintype.card Ω / 2) * Nat.card A ≤ Nat.card (vBeta K1 L2 S Zs) := hG
        _ ≤ 2 * Nat.card E * Nat.card A := hcard
        _ ≤ 2 * 2 ^ (n + 1) * Nat.card A := by gcongr
        _ = 2 ^ (n + 2) * Nat.card A := by ring
    exact Nat.le_of_mul_le_mul_right this hApos
  have key' : Fintype.card Ω / 2 ≤ n + 2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 key
  by_cases hl : IsL2Quot n (OTwoQuot K1)
  · rw [hL hl] at key'
    have h3n := le_three_of_half_le key'
    interval_cases n
    · exact Or.inl hl
    · exact Or.inr hl
  · exact (false_of_half_le hn (hnL hl) key').elim

end CFSG.Quasithin.Background.Harris.R1

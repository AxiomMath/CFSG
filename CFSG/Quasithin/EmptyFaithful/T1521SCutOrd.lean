module

public import CFSG.Quasithin.EmptyFaithful.T1521SCutNum
import CFSG.Quasithin.Background.B69Num
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Quasithin.EmptyFaithful.T1515Concl

public section

namespace CFSG.Quasithin.T1521SCut

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

section Specific

variable {X : Type} [Group X]

theorem card_of_isAlt {k : ℕ} (hk : 2 ≤ k) (h : IsAlt k X) : Nat.card X = Nat.factorial k / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

theorem card_isAlt_six (h : IsAlt 6 X) : Nat.card X = 360 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

theorem card_isAlt_seven (h : IsAlt 7 X) : Nat.card X = 2520 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

theorem card_isPSL_three_two_one (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_isPSL_four_two_one (h : IsPSL 4 2 1 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_isPSL_five_two_one (h : IsPSL 5 2 1 X) : Nat.card X = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h

theorem card_isPSU_three_three_one (h : IsPSU 3 3 1 X) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

end Specific

section Families

variable {X : Type} [Group X]

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  have h2 : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one

theorem famL2 {n : ℕ} (hn : 2 ≤ n) (h : IsPSL 2 2 n X) (hle : Nat.card X ≤ orderBound) :
    Nat.card X ∈ famOrders ∧ (Nat.card X = 20160 → IsPSL 3 2 2 X) := by
  have h1 := B69.card_psl_two_mul h
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.coprime_two_left.mpr (odd_two_pow_sub_one (by omega))
  rw [hg, mul_one] at h1
  have hn12 := l2_le h1 hle
  interval_cases n <;> norm_num at h1 <;>
    refine ⟨by simp only [famOrders, List.mem_cons, List.not_mem_nil, or_false]; omega,
      fun h20 => ?_⟩ <;> first | exact h | (exfalso; omega)

theorem famU3 {n : ℕ} (hn : 2 ≤ n) (h : IsPSU 3 2 n X) (hle : Nat.card X ≤ orderBound) :
    Nat.card X ∈ famOrders ∧ (Nat.card X = 20160 → IsPSL 3 2 2 X) := by
  have h1 := B69.card_psu_three_mul h
  have hg : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hn4 := u3_le hg h1 hle
  interval_cases n <;> norm_num at h1 <;>
    refine ⟨by simp only [famOrders, List.mem_cons, List.not_mem_nil, or_false]; omega,
      fun h20 => ?_⟩ <;> (exfalso; omega)

theorem famL3 {n : ℕ} (h : IsPSL 3 2 n X) (hle : Nat.card X ≤ orderBound) :
    Nat.card X ∈ famOrders ∧ (Nat.card X = 20160 → IsPSL 3 2 2 X) := by
  have hn1 : 1 ≤ n := h.1.2.1
  have h1 := B69.card_psl_three_mul h
  have hg : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hn4 := l3_le hg h1 hle
  interval_cases n <;> norm_num at h1 <;>
    refine ⟨by simp only [famOrders, List.mem_cons, List.not_mem_nil, or_false]; omega,
      fun h20 => ?_⟩ <;> first | exact h | (exfalso; omega)

theorem famSp4 {n : ℕ} (h : IsPSp4 2 n X) (hle : Nat.card X ≤ orderBound) :
    Nat.card X ∈ famOrders ∧ (Nat.card X = 20160 → IsPSL 3 2 2 X) := by
  have hn2 : 2 ≤ n := by
    obtain ⟨⟨-, hm, -, hne⟩, -⟩ := h
    by_contra h1
    have : n = 1 := by omega
    subst this
    exact hne (by decide)
  have h1 := B69.card_psp_four h
  have hn3 := sp4_le h1 hle
  interval_cases n <;> norm_num at h1 <;>
    refine ⟨by simp only [famOrders, List.mem_cons, List.not_mem_nil, or_false]; omega,
      fun h20 => ?_⟩ <;> (exfalso; omega)

theorem famSz {e : ℕ} (h : IsSz e X) (hle : Nat.card X ≤ orderBound) :
    Nat.card X ∈ famOrders ∧ (Nat.card X = 20160 → IsPSL 3 2 2 X) := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e'⟩⟩ := h
  rw [hf] at hK
  have h1 : Nat.card X = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e'.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  have ha3 := sz_le h1 hle
  interval_cases a <;> norm_num at h1 <;>
    refine ⟨by simp only [famOrders, List.mem_cons, List.not_mem_nil, or_false]; omega,
      fun h20 => ?_⟩ <;> (exfalso; omega)

theorem famCases
    (h : IsBender1516 X ∨ (∃ n : ℕ, IsPSL 3 2 n X) ∨ ∃ n : ℕ, IsPSp4 2 n X)
    (hle : Nat.card X ≤ orderBound) :
    Nat.card X ∈ famOrders ∧ (Nat.card X = 20160 → IsPSL 3 2 2 X) := by
  rcases h with (⟨n, hn, h⟩ | ⟨e, h⟩ | ⟨n, hn, h⟩) | ⟨n, h⟩ | ⟨n, h⟩
  · exact famL2 hn h hle
  · exact famSz h hle
  · exact famU3 hn h hle
  · exact famL3 h hle
  · exact famSp4 h hle

end Families

end CFSG.Quasithin.T1521SCut

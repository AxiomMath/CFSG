module

public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129KYb

theorem one_apply_zero_one {F : Type} [Field F] : (1 : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 :=
  Matrix.one_apply_ne (by decide)

theorem one_apply_one_zero {F : Type} [Field F] : (1 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  Matrix.one_apply_ne (by decide)

theorem one_apply_zero_zero {F : Type} [Field F] : (1 : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 :=
  Matrix.one_apply_eq 0

theorem one_apply_one_one {F : Type} [Field F] : (1 : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 :=
  Matrix.one_apply_eq 1

theorem trace_of_order_three {F : Type} [Field F] {M : Matrix (Fin 2) (Fin 2) F}
    (hdet : M.det = 1) (h3 : M ^ 3 = 1) :
    (M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1 → M 0 0 = 1 ∧ M 1 1 = 1) ∧
      (¬ (M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1) → M 0 0 + M 1 1 = -1) := by
  rw [Matrix.det_fin_two] at hdet
  have e00 : (M ^ 3) 0 0 = (1 : Matrix (Fin 2) (Fin 2) F) 0 0 := by rw [h3]
  have e01 : (M ^ 3) 0 1 = (1 : Matrix (Fin 2) (Fin 2) F) 0 1 := by rw [h3]
  have e10 : (M ^ 3) 1 0 = (1 : Matrix (Fin 2) (Fin 2) F) 1 0 := by rw [h3]
  have e11 : (M ^ 3) 1 1 = (1 : Matrix (Fin 2) (Fin 2) F) 1 1 := by rw [h3]
  simp only [pow_three, Matrix.mul_apply, Fin.sum_univ_two, one_apply_zero_zero,
    one_apply_zero_one, one_apply_one_zero, one_apply_one_one] at e00 e01 e10 e11
  have hb : ((M 0 0 + M 1 1) ^ 2 - 1) * M 0 1 = 0 := by
    linear_combination e01 + M 0 1 * hdet
  have hc : ((M 0 0 + M 1 1) ^ 2 - 1) * M 1 0 = 0 := by
    linear_combination e10 + M 1 0 * hdet
  have hd : ((M 0 0 + M 1 1) ^ 2 - 1) * (M 0 0 - M 1 1) = 0 := by
    linear_combination e00 - e11 + (M 0 0 - M 1 1) * hdet
  refine ⟨?_, ?_⟩
  · rintro ⟨hb0, hc0, hd0⟩
    rw [hb0, hc0] at e00 hdet
    have ha3 : M 0 0 ^ 3 = 1 := by linear_combination e00
    rw [← hd0] at hdet
    have ha : M 0 0 = 1 := by linear_combination ha3 - M 0 0 * hdet
    exact ⟨ha, by rw [← hd0, ha]⟩
  · intro hns
    by_cases hs : (M 0 0 + M 1 1) ^ 2 - 1 = 0
    · linear_combination (-1 : F) * e00 + M 0 0 * hs + (-(M 0 0) - (M 0 0 + M 1 1)) * hdet
    · exfalso
      exact hns ⟨(mul_eq_zero.1 hb).resolve_left hs, (mul_eq_zero.1 hc).resolve_left hs,
        sub_eq_zero.1 ((mul_eq_zero.1 hd).resolve_left hs)⟩

theorem sq_entries_of_trace {F : Type} [Field F] {a b c d : F} (hdet : a * d - b * c = 1)
    (htr : a + d = -1) :
    a * a + b * c = -1 - a ∧ a * b + b * d = -b ∧ c * a + d * c = -c ∧
      c * b + d * d = -1 - d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination a * htr - hdet
  · linear_combination b * htr
  · linear_combination c * htr
  · linear_combination d * htr - hdet

theorem commute_decomp {F : Type} [Field F] {M N : Matrix (Fin 2) (Fin 2) F}
    (hns : ¬ (M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1)) (hMN : M * N = N * M) :
    ∃ α β : F, N 0 0 = α + β * M 0 0 ∧ N 0 1 = β * M 0 1 ∧
      N 1 0 = β * M 1 0 ∧ N 1 1 = α + β * M 1 1 := by
  have h00 : (M * N) 0 0 = (N * M) 0 0 := by rw [hMN]
  have h01 : (M * N) 0 1 = (N * M) 0 1 := by rw [hMN]
  have h10 : (M * N) 1 0 = (N * M) 1 0 := by rw [hMN]
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  have E3 : M 0 1 * N 1 0 = N 0 1 * M 1 0 := by linear_combination h00
  have E4 : M 0 1 * (N 0 0 - N 1 1) = N 0 1 * (M 0 0 - M 1 1) := by
    linear_combination (-1 : F) * h01
  have E5 : M 1 0 * (N 0 0 - N 1 1) = N 1 0 * (M 0 0 - M 1 1) := by
    linear_combination h10
  by_cases hb : M 0 1 = 0
  · by_cases hc : M 1 0 = 0
    · have had : M 0 0 - M 1 1 ≠ 0 := fun h => hns ⟨hb, hc, by linear_combination h⟩
      obtain ⟨β, hβ⟩ : ∃ β : F, β * (M 0 0 - M 1 1) = N 0 0 - N 1 1 :=
        ⟨(N 0 0 - N 1 1) / (M 0 0 - M 1 1), div_mul_cancel₀ _ had⟩
      have hy : N 0 1 = 0 := by
        have h' : N 0 1 * (M 0 0 - M 1 1) = 0 := by
          rw [hb] at E4
          linear_combination (-1 : F) * E4
        exact (mul_eq_zero.1 h').resolve_right had
      have hz : N 1 0 = 0 := by
        have h' : N 1 0 * (M 0 0 - M 1 1) = 0 := by
          rw [hc] at E5
          linear_combination (-1 : F) * E5
        exact (mul_eq_zero.1 h').resolve_right had
      refine ⟨N 0 0 - β * M 0 0, β, by ring, ?_, ?_, by linear_combination hβ⟩
      · rw [hb, mul_zero]
        exact hy
      · rw [hc, mul_zero]
        exact hz
    · have hy : N 0 1 = 0 := by
        have h' : N 0 1 * M 1 0 = 0 := by
          rw [hb] at E3
          linear_combination (-1 : F) * E3
        exact (mul_eq_zero.1 h').resolve_right hc
      obtain ⟨β, hβ⟩ : ∃ β : F, β * M 1 0 = N 1 0 :=
        ⟨N 1 0 / M 1 0, div_mul_cancel₀ _ hc⟩
      refine ⟨N 1 1 - β * M 1 1, β, ?_, ?_, hβ.symm, by ring⟩
      · apply mul_left_cancel₀ hc
        linear_combination E5 - (M 0 0 - M 1 1) * hβ
      · rw [hb, mul_zero]
        exact hy
  · obtain ⟨β, hβ⟩ : ∃ β : F, β * M 0 1 = N 0 1 :=
      ⟨N 0 1 / M 0 1, div_mul_cancel₀ _ hb⟩
    refine ⟨N 0 0 - β * M 0 0, β, by ring, hβ.symm, ?_, ?_⟩
    · apply mul_left_cancel₀ hb
      linear_combination E3 - M 1 0 * hβ
    · apply mul_left_cancel₀ hb
      linear_combination (-1 : F) * E4 + (M 0 0 - M 1 1) * hβ

theorem comm_order_three_scalar {F : Type} [Field F] {a b c d x y z w α β : F}
    (h3 : (3 : F) ≠ 0)
    (hdetM : a * d - b * c = 1) (htrM : a + d = -1)
    (hdetN : x * w - y * z = 1) (htrN : x + w = -1)
    (hx : x = α + β * a) (hy : y = β * b) (hz : z = β * c) (hw : w = α + β * d) :
    (x = a ∧ y = b ∧ z = c ∧ w = d) ∨ (x = -1 - a ∧ y = -b ∧ z = -c ∧ w = -1 - d) := by
  subst hx hy hz hw
  have hβ : β = 2 * α + 1 := by linear_combination (-1 : F) * htrN + β * htrM
  have hα : 3 * (α * (α + 1)) = 0 := by
    linear_combination hdetN - α * β * htrM - β ^ 2 * hdetM - (β + α + 1) * hβ
  have hα' : α * (α + 1) = 0 := (mul_eq_zero.1 hα).resolve_left h3
  rcases mul_eq_zero.1 hα' with h0 | h1
  · have hβ1 : β = 1 := by linear_combination hβ + 2 * h0
    left
    rw [h0, hβ1]
    exact ⟨by ring, by ring, by ring, by ring⟩
  · have hα1 : α = -1 := by linear_combination h1
    have hβ1 : β = -1 := by linear_combination hβ + 2 * h1
    right
    rw [hα1, hβ1]
    exact ⟨by ring, by ring, by ring, by ring⟩

theorem commuting_pair {F : Type} [Field F] (h3 : (3 : F) ≠ 0)
    {M N : Matrix (Fin 2) (Fin 2) F} (hdetM : M.det = 1) (hdetN : N.det = 1)
    (hM3 : M ^ 3 = 1) (hN3 : N ^ 3 = 1) (hMN : M * N = N * M)
    (hMns : ¬ (M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1))
    (hNns : ¬ (N 0 1 = 0 ∧ N 1 0 = 0 ∧ N 0 0 = N 1 1)) :
    (N 0 0 = M 0 0 ∧ N 0 1 = M 0 1 ∧ N 1 0 = M 1 0 ∧ N 1 1 = M 1 1) ∨
      (N 0 0 = M 0 0 * M 0 0 + M 0 1 * M 1 0 ∧ N 0 1 = M 0 0 * M 0 1 + M 0 1 * M 1 1 ∧
        N 1 0 = M 1 0 * M 0 0 + M 1 1 * M 1 0 ∧ N 1 1 = M 1 0 * M 0 1 + M 1 1 * M 1 1) := by
  have htrM := (trace_of_order_three hdetM hM3).2 hMns
  have htrN := (trace_of_order_three hdetN hN3).2 hNns
  rw [Matrix.det_fin_two] at hdetM hdetN
  obtain ⟨α, β, hx, hy, hz, hw⟩ := commute_decomp hMns hMN
  rcases comm_order_three_scalar h3 hdetM htrM hdetN htrN hx hy hz hw with
    ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩
  · exact Or.inl ⟨e0, e1, e2, e3⟩
  · obtain ⟨s1, s2, s3, s4⟩ := sq_entries_of_trace hdetM htrM
    refine Or.inr ⟨?_, ?_, ?_, ?_⟩
    · linear_combination e0 - s1
    · linear_combination e1 - s2
    · linear_combination e2 - s3
    · linear_combination e3 - s4

theorem sl_eq_of_entries {F : Type} [Field F] {g h : Matrix.SpecialLinearGroup (Fin 2) F}
    (h00 : (h : Matrix (Fin 2) (Fin 2) F) 0 0 = (g : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) F) 0 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 1)
    (h10 : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = (g : Matrix (Fin 2) (Fin 2) F) 1 0)
    (h11 : (h : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 1 1) :
    h = g := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem sl_eq_one_of_entries {F : Type} [Field F] {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1)
    (h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)
    (h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1) :
    g = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem sq_apply_sl {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (i j : Fin 2) :
    ((g ^ 2 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      ∑ k, (g : Matrix (Fin 2) (Fin 2) F) i k * (g : Matrix (Fin 2) (Fin 2) F) k j := by
  rw [Matrix.SpecialLinearGroup.coe_pow, sq, Matrix.mul_apply]

theorem eq_or_eq_sq_of_mem {F : Type} [Field F] (h3 : (3 : F) ≠ 0)
    {g h : Matrix.SpecialLinearGroup (Fin 2) F} (hg3 : g ^ 3 = 1) (hh3 : h ^ 3 = 1)
    (hgh : g * h = h * g) (hg1 : g ≠ 1) (hh1 : h ≠ 1) : h = g ∨ h = g ^ 2 := by
  have hM3 : (g : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hg3, Matrix.SpecialLinearGroup.coe_one]
  have hN3 : (h : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hh3, Matrix.SpecialLinearGroup.coe_one]
  have hMN : (g : Matrix (Fin 2) (Fin 2) F) * h = h * g := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hgh]
  have hMns : ¬ ((g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (g : Matrix (Fin 2) (Fin 2) F) 1 1) := by
    rintro ⟨h01, h10, h00⟩
    obtain ⟨e00, e11⟩ := (trace_of_order_three g.2 hM3).1 ⟨h01, h10, h00⟩
    exact hg1 (sl_eq_one_of_entries e00 h01 h10 e11)
  have hNns : ¬ ((h : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
      (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (h : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 1) := by
    rintro ⟨h01, h10, h00⟩
    obtain ⟨e00, e11⟩ := (trace_of_order_three h.2 hN3).1 ⟨h01, h10, h00⟩
    exact hh1 (sl_eq_one_of_entries e00 h01 h10 e11)
  rcases commuting_pair h3 g.2 h.2 hM3 hN3 hMN hMns hNns with
    ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩
  · exact Or.inl (sl_eq_of_entries e0 e1 e2 e3)
  · refine Or.inr (sl_eq_of_entries ?_ ?_ ?_ ?_) <;> rw [sq_apply_sl, Fin.sum_univ_two]
    · exact e0
    · exact e1
    · exact e2
    · exact e3

theorem three_ne_zero_of_not_dvd {F : Type} [Field F] [Finite F] (h3 : ¬ 3 ∣ Nat.card F) :
    (3 : F) ≠ 0 := by
  intro h
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hdvd : ringChar F ∣ 3 := by
    rw [← CharP.cast_eq_zero_iff F (ringChar F) 3]
    exact_mod_cast h
  have hp3 : ringChar F = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
  apply h3
  rw [Nat.card_eq_fintype_card, hcard, hp3]
  exact dvd_pow_self 3 n.ne_zero

theorem card_le_three_of_isElemAbelian_sl2 {F : Type} [Field F] [Finite F]
    (h3 : ¬ 3 ∣ Nat.card F)
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have h3F : (3 : F) ≠ 0 := three_ne_zero_of_not_dvd h3
  by_cases hex : ∃ g ∈ E, g ≠ 1
  · obtain ⟨g, hgE, hg1⟩ := hex
    have hg3 : g ^ 3 = 1 := hE.2 g hgE
    have hle : E ≤ Subgroup.zpowers g := by
      intro h hhE
      by_cases hh1 : h = 1
      · rw [hh1]
        exact Subgroup.one_mem _
      · have hh3 : h ^ 3 = 1 := hE.2 h hhE
        have hgh : g * h = h * g :=
          congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hgE⟩ ⟨h, hhE⟩)
        rcases eq_or_eq_sq_of_mem h3F hg3 hh3 hgh hg1 hh1 with rfl | rfl
        · exact Subgroup.mem_zpowers _
        · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    calc Nat.card E ≤ Nat.card (Subgroup.zpowers g) := Subgroup.card_le_of_le hle
      _ = orderOf g := Nat.card_zpowers g
      _ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hg3
  · push_neg at hex
    rw [(Subgroup.eq_bot_iff_forall E).2 hex, Subgroup.card_bot]
    norm_num

end CFSG.RankThree.PartTwo.Sec12.Hering129KYb

end

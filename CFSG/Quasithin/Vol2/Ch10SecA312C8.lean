module

public import CFSG.Quasithin.Vol2.Ch10SecA312C6
public import CFSG.Quasithin.Vol2.Ch10SecA312C7
public import CFSG.Quasithin.Vol2.Ch10SecA312C5

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def SylowTest (X : Type) [Group X] (B : Subgroup X) : Prop :=
  ∀ r k : ℕ, r.Prime → r ≠ 2 → 1 ≤ k → r ^ k ∣ Nat.card B → ¬ r ^ (k + 1) ∣ Nat.card X → False

variable {X : Type} [Group X] {B : Subgroup X}

theorem card_top_of {n : ℕ} (h : Nat.card ↥(⊤ : Subgroup X) = n) : Nat.card X = n := by
  rwa [Subgroup.card_top] at h

theorem test_modO2 (hK : SylowTest X B) {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : 1 ≤ k)
    (h1 : r ^ k ∣ Nat.card (ModO2 B)) (h2 : ¬ r ^ (k + 1) ∣ Nat.card X) : False :=
  hK r k hr hr2 hk (h1.trans (Subgroup.card_quotient_dvd_card _)) h2

theorem test_ext (hK : SylowTest X B) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY) {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : 1 ≤ k)
    (hY : ∀ (Q : Type) [Group Q], PY Q → r ^ k ∣ Nat.card Q) (h2 : ¬ r ^ (k + 1) ∣ Nat.card X) :
    False := by
  obtain ⟨V, _, hQ, hd⟩ := card_quotient_dvd_of_isExt h
  exact hK r k hr hr2 hk ((hY _ hQ).trans hd) h2

theorem case4 (hK : SylowTest X B) (h : A312C4 B ⊤) : False := by
  obtain ⟨hB, hL | hL, -⟩ := h
  · exact test_modO2 hK (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (by rw [card_l32 hB]; norm_num) (by rw [card_top_of (card_l42 hL)]; norm_num)
  · exact test_modO2 hK (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (by rw [card_l32 hB]; norm_num) (by rw [card_top_of (card_l52 hL)]; norm_num)

theorem case5 (hK : SylowTest X B) (h : A312C5 B ⊤) : False := by
  obtain ⟨hB, hL, -⟩ := h
  exact test_modO2 hK (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
    (by rw [card_l42 hB]; norm_num) (by rw [card_top_of (card_l52 hL)]; norm_num)

theorem case6 (hK : SylowTest X B) (h : A312C6 B ⊤) : False := by
  obtain ⟨hB | hB, hL⟩ := h
  · refine hK 5 1 (by norm_num) (by norm_num) le_rfl (by rw [card_alt5 hB]; norm_num) ?_
    rcases hL with hL | hL
    · rw [card_top_of (card_alt7 hL)]; norm_num
    · rw [card_top_of (card_hat7 hL)]; norm_num
  · refine hK 7 1 (by norm_num) (by norm_num) le_rfl (by rw [card_l32 hB]; norm_num) ?_
    rcases hL with hL | hL
    · rw [card_top_of (card_alt7 hL)]; norm_num
    · rw [card_top_of (card_hat7 hL)]; norm_num

theorem case7 (hK : SylowTest X B) (h : A312C7 B ⊤) : False := by
  rcases h with ⟨hB, hL⟩ | ⟨hB, hL⟩
  · exact hK 5 1 (by norm_num) (by norm_num) le_rfl (by rw [card_alt6 hB]; norm_num)
      (by rw [card_top_of (card_alt7 hL)]; norm_num)
  · exact hK 5 1 (by norm_num) (by norm_num) le_rfl (by rw [card_hat6 hB]; norm_num)
      (by rw [card_top_of (card_hat7 hL)]; norm_num)

theorem case8 [Finite X] (hK : SylowTest X B) (hs : ¬ A312PairStructCase B)
    (h : A312C8 B ⊤) : False := by
  rcases h with ⟨p, hp, hp3, hB, hL⟩ | ⟨hB, p, hp, hL, h5, h8⟩
  · obtain ⟨k, hk, h1, h2⟩ := psl2_sq_three hp hp3 hB hL
    exact hK 3 k Nat.prime_three (by norm_num) hk h1 (by rwa [← Subgroup.card_top])
  · have hp3 : p ≠ 3 := by rintro rfl; norm_num at h5
    have hp5 : p ≠ 5 := by rintro rfl; norm_num at h5
    by_cases h9 : 9 ∣ p ^ 2 - 1
    · by_cases h25 : 25 ∣ p ^ 2 - 1
      · exact hs (Or.inr (Or.inr (Or.inl ⟨hB, p, hp, hL, h5, h8, h9, h25⟩)))
      · exact hK 5 1 (by norm_num) (by norm_num) le_rfl (by rw [card_alt5 hB]; norm_num)
          (by rw [← Subgroup.card_top]
              exact psl2_not_dvd hp (by norm_num) (Ne.symm hp5) h25 hL)
    · exact hK 3 1 Nat.prime_three (by norm_num) le_rfl (by rw [card_alt5 hB]; norm_num)
        (by rw [← Subgroup.card_top]
            exact psl2_not_dvd hp Nat.prime_three (Ne.symm hp3) h9 hL)

theorem case10 [Finite X] (hK : SylowTest X B) (h : A312C10 B ⊤) : False := by
  obtain ⟨p, hp, hp3, ⟨V, _, hV, hQ⟩, hL⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ⟩ := hV
  have hVc : Nat.card V = p ^ 2 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
  have hB : p ^ 3 ∣ Nat.card B := by
    rw [V.card_eq_card_quotient_mul_card_subgroup, hVc, card_of_isSL2 hQ]
    exact ⟨p ^ 2 - 1, by ring⟩
  have hr2 : p ≠ 2 := by omega
  exact hK p 3 hp hr2 (by norm_num) hB (by rw [← Subgroup.card_top]; exact l3_not_dvd_p hp hL)

end CFSG.Quasithin.Vol2.Ch10.A312C

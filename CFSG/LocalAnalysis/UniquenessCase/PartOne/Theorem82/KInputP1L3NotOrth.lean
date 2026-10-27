module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeFactsOrth
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3Order
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3OrthArith
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3Small
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3TwoAdic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.HardMathSupport.Curtis.Coordinator.PLType

theorem center_eq_bot_of_mulEquiv {X S : Type} [Group X] [Group S] (e : X ≃* S)
    (h : Subgroup.center S = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' : e x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (hx z)
  have hx1 : e x = 1 := by simpa [h] using hx'
  exact e.injective (by rw [hx1, map_one])

theorem card_quotient_center_of_eq_bot {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
  have hcard : Nat.card (Subgroup.center X) = 1 := by rw [h, Subgroup.card_bot]
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [hcard, mul_one] at hc
  exact hc.symm

theorem eq_card_of_quotient_center {X S : Type} [Group X] [Group S] {N : ℕ} (e : X ≃* S)
    (hZ : Subgroup.center S = ⊥) (hY : Nat.card (X ⧸ Subgroup.center X) = N) :
    N = Nat.card S := by
  have hZX : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv e hZ
  have hcardX : Nat.card X = N := by rw [← card_quotient_center_of_eq_bot hZX, hY]
  exact hcardX.symm.trans (Nat.card_congr e.toEquiv)

theorem order_ne_orth {q c m c' : ℕ} (hq : (q % 2 = 1 ∧ 5 ≤ q) ∨ ∃ f : ℕ, 1 ≤ f ∧ q = 2 ^ f)
    (hc : c = q ^ 3 - 1 ∨ c = q ^ 3 + 1) (hm : 4 ≤ m) (hc' : c' = 2 ^ m - 1 ∨ c' = 2 ^ m + 1) :
    q ^ 3 * ((q ^ 2 - 1) * c) ≠
      2 ^ (m * (m - 1)) * c' * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1) := by
  rcases hq with ⟨hqodd, hq5⟩ | ⟨f, hf, rfl⟩
  · intro h
    have hc'le : c' ≤ 2 ^ m + 1 := by
      rcases hc' with rfl | rfl
      exacts [(Nat.sub_le _ _).trans (Nat.le_succ _), le_rfl]
    have hP := orth_odd_part_lt hm hc'le
    have hdvd : 2 ^ (m * (m - 1)) ∣ q ^ 3 * ((q ^ 2 - 1) * c) := by
      rw [h, mul_assoc]
      exact dvd_mul_right _ _
    have h3 := two_pow_three_mul_le hqodd hq5 hc hdvd
    have hlt : q ^ 3 * ((q ^ 2 - 1) * c) < 2 ^ (3 * (m * (m - 1))) := by
      rw [h, mul_assoc]
      calc 2 ^ (m * (m - 1)) * (c' * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1))
          < 2 ^ (m * (m - 1)) * 2 ^ (2 * (m * (m - 1))) :=
            Nat.mul_lt_mul_of_pos_left hP (by positivity)
        _ = 2 ^ (3 * (m * (m - 1))) := by
            rw [← pow_add]
            congr 1
            ring
    omega
  · exact orth_order_ne hf hm hc' hc

theorem not_isOrthogonalTwo {X : Type} [Group X] {q c : ℕ}
    (hq : (q % 2 = 1 ∧ 5 ≤ q) ∨ ∃ f : ℕ, 1 ≤ f ∧ q = 2 ^ f)
    (hc : c = q ^ 3 - 1 ∨ c = q ^ 3 + 1)
    (hY : Nat.card (X ⧸ Subgroup.center X) = q ^ 3 * ((q ^ 2 - 1) * c)) :
    ¬ CFSG.AGLEmbedding.IsOrthogonalTwo X := by
  have hq2 : 2 ≤ q := by
    rcases hq with ⟨-, h5⟩ | ⟨f, hf, rfl⟩
    · omega
    · simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hf
  intro horth
  unfold CFSG.AGLEmbedding.IsOrthogonalTwo at horth
  rcases horth with ⟨d, ⟨m, p, hp, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd with hd | hd | ⟨-, hd⟩
    · have hm : 4 ≤ m := four_le_of_valid_D (hd ▸ d.2)
      have hZ := (tauCetiOrthFacts_holds.1 m d ⟨p, hp, Or.inl hd⟩).1
      exact order_ne_orth hq hc hm (Or.inl rfl)
        ((eq_card_of_quotient_center e hZ hY).trans (card_lie_typeD_two m d p hp hd))
    · have hm : 4 ≤ m := four_le_of_valid_twistedD (hd ▸ d.2)
      have hZ := (tauCetiOrthFacts_holds.1 m d ⟨p, hp, Or.inr hd⟩).1
      exact order_ne_orth hq hc hm (Or.inr rfl)
        ((eq_card_of_quotient_center e hZ hY).trans (card_lie_twistedD_two m d p hp hd))
    · have hZ := (tauCetiOrthFacts_holds.2 d ⟨p, hp, hd⟩).1
      have hsmall : q ^ 3 * ((q ^ 2 - 1) * c) = 25920 :=
        (eq_card_of_quotient_center e hZ hY).trans (card_lie_twistedA_three_two d p hp hd)
      exact order_not_small hq2 hc (Or.inr (Or.inr (Or.inr hsmall)))
  · have hZ := center_alt_fin_small hn
    have hcard := eq_card_of_quotient_center e hZ hY
    rcases card_alt_fin_small hn with h60 | h360 | h20160
    · exact order_not_small hq2 hc (Or.inl (hcard.trans h60))
    · exact order_not_small hq2 hc (Or.inr (Or.inl (hcard.trans h360)))
    · exact order_not_small hq2 hc (Or.inr (Or.inr (Or.inl (hcard.trans h20160))))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

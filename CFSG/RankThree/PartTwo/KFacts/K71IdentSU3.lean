module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3
import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Orders

variable {K : Type} [Field K] [Fintype K]

theorem card_SL_mul_card_sub_one (n : ℕ) [NeZero n] :
    Nat.card (SpecialLinearGroup (Fin n) K) * (Fintype.card K - 1) =
      ∏ i : Fin n, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ)) := by
  have h1 := card_SL_mul_card_units (n := Fin n) (R := K)
  rw [card_GL_field, Nat.card_units, Nat.card_eq_fintype_card (α := K)] at h1
  exact h1

theorem pow_dvd_card_SL (n : ℕ) [NeZero n] :
    Fintype.card K ^ (n * (n - 1) / 2) ∣ Nat.card (SpecialLinearGroup (Fin n) K) := by
  set k := Fintype.card K with hk
  have hk1 : 1 < k := Fintype.one_lt_card
  have hdvd : k ^ (n * (n - 1) / 2) ∣ ∏ i : Fin n, (k ^ n - k ^ (i : ℕ)) := by
    have h1 : ∏ i : Fin n, k ^ (i : ℕ) ∣ ∏ i : Fin n, (k ^ n - k ^ (i : ℕ)) := by
      apply Finset.prod_dvd_prod_of_dvd
      intro i _
      have hi : (i : ℕ) ≤ n := i.2.le
      refine ⟨k ^ (n - i) - 1, ?_⟩
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi]
    have h2 : ∏ i : Fin n, k ^ (i : ℕ) = k ^ (n * (n - 1) / 2) := by
      rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) n,
        Finset.sum_range_id]
    rwa [h2] at h1
  rw [← card_SL_mul_card_sub_one] at hdvd
  have hcop : Nat.Coprime (k ^ (n * (n - 1) / 2)) (k - 1) := by
    apply Nat.Coprime.pow_left
    have : k = (k - 1) + 1 := by omega
    rw [Nat.coprime_comm]
    nth_rewrite 2 [this]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem card_SL_lt (n : ℕ) [NeZero n] :
    Nat.card (SpecialLinearGroup (Fin n) K) < Fintype.card K ^ (n ^ 2) := by
  set k := Fintype.card K with hk
  have hk1 : 1 < k := Fintype.one_lt_card
  have hprod : ∏ i : Fin n, (k ^ n - k ^ (i : ℕ)) < k ^ (n ^ 2) := by
    have hle : ∏ i : Fin n, (k ^ n - k ^ (i : ℕ)) ≤ ∏ _i : Fin n, (k ^ n - 1) := by
      refine Finset.prod_le_prod fun i _ => ?_
      have : 1 ≤ k ^ (i : ℕ) := Nat.one_le_pow _ _ (by omega)
      omega
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hle
    have hkn : 1 ≤ k ^ n := Nat.one_le_pow _ _ (by omega)
    calc ∏ i : Fin n, (k ^ n - k ^ (i : ℕ)) ≤ (k ^ n - 1) ^ n := hle
      _ < (k ^ n) ^ n := Nat.pow_lt_pow_left (by omega) (NeZero.ne n)
      _ = k ^ (n ^ 2) := by rw [← pow_mul, sq]
  calc Nat.card (SpecialLinearGroup (Fin n) K)
      ≤ Nat.card (SpecialLinearGroup (Fin n) K) * (k - 1) := Nat.le_mul_of_pos_right _ (by omega)
    _ = ∏ i : Fin n, (k ^ n - k ^ (i : ℕ)) := card_SL_mul_card_sub_one n
    _ < k ^ (n ^ 2) := hprod

theorem card_SL_lt_pow_sub_one {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (SpecialLinearGroup (Fin n) K) < Fintype.card K ^ (n ^ 2 - 1) := by
  have hk1 : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have h := card_SL_mul_card_sub_one (K := K) (n' + 1)
  rw [Fin.prod_univ_castSucc] at h
  simp only [Fin.val_castSucc, Fin.val_last] at h
  generalize Fintype.card K = k at h hk1 ⊢
  generalize Nat.card (SpecialLinearGroup (Fin (n' + 1)) K) = N at h ⊢
  have hlast : k ^ (n' + 1) - k ^ n' = k ^ n' * (k - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_succ]
  rw [hlast, ← mul_assoc] at h
  have hN : N = (∏ i : Fin n', (k ^ (n' + 1) - k ^ (i : ℕ))) * k ^ n' :=
    Nat.eq_of_mul_eq_mul_right (by omega) h
  rw [hN]
  have hstrict : ∏ i : Fin n', (k ^ (n' + 1) - k ^ (i : ℕ)) < (k ^ (n' + 1)) ^ n' := by
    have hk' : 1 ≤ k ^ (n' + 1) := Nat.one_le_pow _ _ (by omega)
    calc ∏ i : Fin n', (k ^ (n' + 1) - k ^ (i : ℕ)) ≤ ∏ _i : Fin n', (k ^ (n' + 1) - 1) :=
          Finset.prod_le_prod fun i _ => by
            have : 1 ≤ k ^ (i : ℕ) := Nat.one_le_pow _ _ (by omega)
            omega
      _ = (k ^ (n' + 1) - 1) ^ n' := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ < (k ^ (n' + 1)) ^ n' := Nat.pow_lt_pow_left (by omega) (by omega)
  have hexp : (n' + 1) ^ 2 - 1 = (n' + 1) * n' + n' := by
    rw [show (n' + 1) ^ 2 = (n' + 1) * n' + n' + 1 by ring]
    omega
  have hpow : k ^ ((n' + 1) * n' + n') = (k ^ (n' + 1)) ^ n' * k ^ n' := by
    rw [pow_add, pow_mul]
  rw [hexp, hpow]
  exact Nat.mul_lt_mul_of_pos_right hstrict (by positivity)

theorem card_SL_three :
    Nat.card (SpecialLinearGroup (Fin 3) K) =
      Fintype.card K ^ 3 * (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 3 - 1) := by
  have hk1 : 1 < Fintype.card K := Fintype.one_lt_card
  have h := card_SL_mul_card_sub_one (K := K) 3
  rw [Fin.prod_univ_three] at h
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h
  have hpos : 0 < Fintype.card K - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h]
  have h2 : 1 ≤ Fintype.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Fintype.card K ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hk2 : Fintype.card K ≤ Fintype.card K ^ 3 := Nat.le_self_pow (by norm_num) _
  have hk3 : Fintype.card K ^ 2 ≤ Fintype.card K ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  zify [h2, h3, hk2, hk3, hk1.le]
  ring

end Orders

section UnitaryOrder

variable {p f : ℕ} {K : Type} [Field K]

theorem card_unitarySU_three (h : UnitaryFieldData p f K) :
    Nat.card (unitarySU p f K 3) = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  have := h.finite
  have hsymm : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm :=
    gramForm_isSymm h (by simp [Matrix.map_one])
  have hsep : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hsymm hsep
    (Module.finrank_fin_fun K) (by norm_num)).2.1
  rw [unitarySU_eq_gramSU h, card_gramSU]
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
    ring
  rw [hprod] at hSU
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  zify [hq2]
  rw [hSU]
  norm_num
  ring

theorem su3Order_lt {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) :
    x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) < y ^ 3 * (y ^ 2 - 1) * (y ^ 3 + 1) := by
  have hy : 2 ≤ y := by omega
  have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  have hy2 : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hxy2 : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left hxy (by norm_num)
  have hxy3 : x ^ 3 < y ^ 3 := Nat.pow_lt_pow_left hxy (by norm_num)
  have h1 : x ^ 2 - 1 < y ^ 2 - 1 := by omega
  calc x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) ≤ y ^ 3 * (x ^ 2 - 1) * (y ^ 3 + 1) := by
        gcongr
    _ < y ^ 3 * (y ^ 2 - 1) * (y ^ 3 + 1) := by
        have : 0 < y ^ 3 := by positivity
        gcongr

theorem su3Order_injective {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) = y ^ 3 * (y ^ 2 - 1) * (y ^ 3 + 1)) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (su3Order_lt hx hxy).ne
  · exact hxy
  · exact absurd h (su3Order_lt hy hxy).ne'

end UnitaryOrder

section SLOrder

theorem prime_pow_dvd_of_dvd_mul_three {ℓ v A B C : ℕ} (hℓ : ℓ.Prime)
    (hAB : ¬ (ℓ ∣ A ∧ ℓ ∣ B)) (hAC : ¬ (ℓ ∣ A ∧ ℓ ∣ C)) (hBC : ¬ (ℓ ∣ B ∧ ℓ ∣ C))
    (h : ℓ ^ v ∣ A * (B * C)) : ℓ ^ v ∣ A ∨ ℓ ^ v ∣ B ∨ ℓ ^ v ∣ C := by
  have cop : ∀ {X : ℕ}, ¬ ℓ ∣ X → Nat.Coprime (ℓ ^ v) X := fun hX =>
    Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hX)
  by_cases hA : ℓ ∣ A
  · have hB : ¬ ℓ ∣ B := fun hB => hAB ⟨hA, hB⟩
    have hC : ¬ ℓ ∣ C := fun hC => hAC ⟨hA, hC⟩
    have hBC' : ¬ ℓ ∣ B * C := fun h' => (hℓ.dvd_mul.mp h').elim hB hC
    exact Or.inl ((cop hBC').dvd_of_dvd_mul_right h)
  · have h1 := (cop hA).dvd_of_dvd_mul_left h
    by_cases hC : ℓ ∣ C
    · have hB : ¬ ℓ ∣ B := fun hB => hBC ⟨hB, hC⟩
      exact Or.inr (Or.inr ((cop hB).dvd_of_dvd_mul_left h1))
    · exact Or.inr (Or.inl ((cop hC).dvd_of_dvd_mul_right h1))

theorem pow_fifteen_le_sq_su3Order {Q : ℕ} (hQ : 2 ≤ Q) :
    Q ^ 15 ≤ (Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1)) ^ 2 := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : Q ^ 3 ≤ (Q ^ 2 - 1) ^ 2 := by
    zify [h2]
    have hQ' : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
    nlinarith [pow_pos (show (0 : ℤ) < Q by omega) 2, pow_pos (show (0 : ℤ) < Q by omega) 3]
  calc Q ^ 15 = (Q ^ 6) ^ 2 * Q ^ 3 := by ring
    _ ≤ (Q ^ 6) ^ 2 * (Q ^ 2 - 1) ^ 2 := Nat.mul_le_mul_left _ h3
    _ = (Q ^ 3 * (Q ^ 2 - 1) * Q ^ 3) ^ 2 := by ring
    _ ≤ (Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1)) ^ 2 := by gcongr; omega

theorem lt_su3Order {Q : ℕ} (hQ : 8 ≤ Q) : (Q + 1) ^ 6 < Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h2]
  have hQ' : (8 : ℤ) ≤ Q := by exact_mod_cast hQ
  have h0 : (0 : ℤ) < Q := by omega
  nlinarith [pow_pos h0 2, pow_pos h0 3, pow_pos h0 4, pow_pos h0 5, pow_pos h0 6, pow_pos h0 7,
    mul_le_mul_of_nonneg_left hQ' (pow_pos h0 7).le]

theorem su3Order_factor {Q : ℕ} (hQ : 1 ≤ Q) :
    (Q ^ 2 - 1) * (Q ^ 3 + 1) = (Q - 1) * ((Q + 1) ^ 2 * (Q ^ 2 - Q + 1)) := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  have hQQ : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  zify [h2, hQ, hQQ]
  ring

theorem card_SL_ne_su3Order {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Fintype K]
    (hK3 : ringChar K ≠ 3) {Q m : ℕ} (hQ : Q = 2 ^ m) (hQ8 : 8 ≤ Q) :
    Nat.card (SpecialLinearGroup (Fin n) K) ≠ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
  intro heq
  have : NeZero n := ⟨by omega⟩
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [hQ, h0] at hQ8; norm_num at hQ8
    · exact h0
  have hQeven : 2 ∣ Q := by rw [hQ]; exact dvd_pow_self 2 (by omega)
  have hN0 := pow_dvd_card_SL (K := K) n
  have hlt0 := card_SL_lt (K := K) n
  have hlt1 := card_SL_lt_pow_sub_one (K := K) (n := n) (by omega)
  have h30 : n = 3 → Nat.card (SpecialLinearGroup (Fin n) K) =
      Fintype.card K ^ 3 * (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 3 - 1) := by
    rintro rfl
    exact card_SL_three
  have hk1 : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨ℓ, hchar, b, hℓ, hk⟩ := FiniteField.card' K
  have := hchar
  have hringChar : ringChar K = ℓ := ringChar.eq K ℓ
  rw [heq] at hN0 hlt0 hlt1
  generalize Fintype.card K = k at hN0 hlt0 hlt1 h30 hk1 hk
  set e := n * (n - 1) / 2 with he
  have he2 : 2 * e = n * (n - 1) := by
    rw [he]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  have hQQ : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  have hN : k ^ e ∣ Q ^ 3 * ((Q - 1) * ((Q + 1) ^ 2 * (Q ^ 2 - Q + 1))) := by
    rw [← su3Order_factor (by omega), ← mul_assoc]
    exact hN0
  have hkℓ : k ^ e = ℓ ^ ((b : ℕ) * e) := by rw [hk, ← pow_mul]
  have hodd : ¬ 2 ∣ (Q - 1) * ((Q + 1) ^ 2 * (Q ^ 2 - Q + 1)) := by
    rw [Nat.prime_two.dvd_mul, Nat.prime_two.dvd_mul]
    rintro (h | h | h)
    · omega
    · have := Nat.prime_two.dvd_of_dvd_pow h
      omega
    · obtain ⟨t, ht⟩ := hQeven
      have h' : 2 ∣ Q ^ 2 - Q := ⟨2 * t ^ 2 - t, by rw [ht]; ring_nf; omega⟩
      omega
  have hpos : 0 < Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
    have : 1 < Q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    have : 0 < Q ^ 2 - 1 := by omega
    positivity
  by_cases hℓ2 : ℓ = 2
  ·
    subst hℓ2
    have hcop : Nat.Coprime (k ^ e) ((Q - 1) * ((Q + 1) ^ 2 * (Q ^ 2 - Q + 1))) := by
      rw [hkℓ]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    have hle : k ^ e ≤ Q ^ 3 :=
      Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hN)
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    ·
      obtain rfl : n = 3 := by omega
      have he3 : e = 3 := by omega
      rw [he3] at hle
      have hkQ : k ≤ Q := (Nat.pow_le_pow_iff_left (by norm_num)).mp hle
      have h3 := h30 rfl
      rw [heq] at h3
      have hk3 : k ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left hkQ 3
      have hk2 : k ^ 2 - 1 ≤ Q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hkQ 2) 1
      have hQ2 : 1 < Q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
      have : k ^ 3 * (k ^ 2 - 1) * (k ^ 3 - 1) < Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
        calc k ^ 3 * (k ^ 2 - 1) * (k ^ 3 - 1) ≤ Q ^ 3 * (Q ^ 2 - 1) * (k ^ 3 - 1) := by
              gcongr
          _ < Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
              have : 0 < Q ^ 3 * (Q ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
              exact Nat.mul_lt_mul_of_pos_left (by omega) this
      omega
    ·
      set S := Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) with hS
      have hexp : (n ^ 2 - 1) * n = e * (2 * (n + 1)) := by
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
        have h1 : (n' + 4) ^ 2 - 1 = (n' + 5) * (n' + 3) := by
          rw [show (n' + 4) ^ 2 = n' * n' + 8 * n' + 16 by ring]
          rw [show (n' + 5) * (n' + 3) = n' * n' + 8 * n' + 15 by ring]
          omega
        have h2 : 2 * e = (n' + 4) * (n' + 3) := by
          rw [he2, show n' + 4 - 1 = n' + 3 by omega]
        rw [h1]
        nlinarith
      have h1 : S ^ n < Q ^ (6 * (n + 1)) := by
        calc S ^ n < (k ^ (n ^ 2 - 1)) ^ n := Nat.pow_lt_pow_left hlt1 (by omega)
          _ = (k ^ e) ^ (2 * (n + 1)) := by rw [← pow_mul, ← pow_mul, hexp]
          _ ≤ (Q ^ 3) ^ (2 * (n + 1)) := Nat.pow_le_pow_left hle _
          _ = Q ^ (6 * (n + 1)) := by rw [← pow_mul]; ring_nf
      have h2 : Q ^ (15 * n) ≤ S ^ (2 * n) := by
        calc Q ^ (15 * n) = (Q ^ 15) ^ n := by rw [← pow_mul]
          _ ≤ (S ^ 2) ^ n := Nat.pow_le_pow_left (pow_fifteen_le_sq_su3Order (by omega)) n
          _ = S ^ (2 * n) := by rw [← pow_mul]
      have h3 : S ^ (2 * n) < Q ^ (12 * (n + 1)) := by
        calc S ^ (2 * n) = (S ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
          _ < (Q ^ (6 * (n + 1))) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
          _ = Q ^ (12 * (n + 1)) := by rw [← pow_mul]; ring_nf
      have h4 : Q ^ (12 * (n + 1)) ≤ Q ^ (15 * n) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  ·
    have hℓ3 : ℓ ≠ 3 := fun h3 => hK3 (hringChar.trans h3)
    have hℓQ : ¬ ℓ ∣ Q := fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
      (hℓ.dvd_of_dvd_pow (hQ ▸ h)))
    have hcop : Nat.Coprime (k ^ e) (Q ^ 3) := by
      rw [hkℓ]
      exact Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓQ)
    have hN' : ℓ ^ ((b : ℕ) * e) ∣ (Q - 1) * ((Q + 1) ^ 2 * (Q ^ 2 - Q + 1)) := by
      rw [← hkℓ]
      exact hcop.dvd_of_dvd_mul_left hN
    have hcases := prime_pow_dvd_of_dvd_mul_three (v := (b : ℕ) * e) hℓ
      (fun ⟨h1, h2⟩ => by
        have h2' := hℓ.dvd_of_dvd_pow h2
        have : ℓ ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub h2' h1
        rw [show (Q + 1) - (Q - 1) = 2 by omega] at this
        exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this))
      (fun ⟨h1, h2⟩ => by
        have hle1 : Q * (Q - 1) ≤ Q ^ 2 - Q + 1 := by
          have : Q * (Q - 1) = Q ^ 2 - Q := by
            rw [Nat.mul_sub, mul_one, sq]
          omega
        have : ℓ ∣ (Q ^ 2 - Q + 1) - Q * (Q - 1) := Nat.dvd_sub h2 (Dvd.dvd.mul_left h1 Q)
        rw [show (Q ^ 2 - Q + 1) - Q * (Q - 1) = 1 by
          have : Q * (Q - 1) = Q ^ 2 - Q := by rw [Nat.mul_sub, mul_one, sq]
          omega] at this
        exact hℓ.one_lt.ne' (Nat.dvd_one.mp this))
      (fun ⟨h1, h2⟩ => by
        have h1' := hℓ.dvd_of_dvd_pow h1
        have hid : (Q + 1) * (Q - 2) + 3 = Q ^ 2 - Q + 1 := by
          zify [hQQ, (by omega : 2 ≤ Q)]
          ring
        have : ℓ ∣ (Q ^ 2 - Q + 1) - (Q + 1) * (Q - 2) :=
          Nat.dvd_sub h2 (Dvd.dvd.mul_right h1' (Q - 2))
        rw [show (Q ^ 2 - Q + 1) - (Q + 1) * (Q - 2) = 3 by omega] at this
        exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp this)) hN'
    have hsq : (Q + 1) ^ 2 = Q ^ 2 + 2 * Q + 1 := by ring
    have hle : k ^ e ≤ (Q + 1) ^ 2 := by
      rw [hkℓ]
      rcases hcases with h | h | h
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
      · exact Nat.le_of_dvd (by positivity) h
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    have hexp : n ^ 2 ≤ 3 * e := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
      have h2 : 2 * e = (n' + 3) * (n' + 2) := by
        rw [he2, show n' + 3 - 1 = n' + 2 by omega]
      nlinarith
    have h1 : Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) < (Q + 1) ^ 6 := by
      calc Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 + 1) < k ^ (n ^ 2) := hlt0
        _ ≤ k ^ (3 * e) := Nat.pow_le_pow_right (by omega) hexp
        _ = (k ^ e) ^ 3 := by rw [← pow_mul, mul_comm]
        _ ≤ ((Q + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hle 3
        _ = (Q + 1) ^ 6 := by rw [← pow_mul]
    have h2 := lt_su3Order hQ8
    omega

end SLOrder

section Center

theorem exists_mem_center_statedSU_ne_one {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) (h3 : 3 ∣ 2 ^ m + 1) :
    ∃ z ∈ Subgroup.center (unitarySU 2 m K 3), z ≠ 1 ∧ z ^ 3 = 1 := by
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = (2 ^ m + 1) * (2 ^ m - 1) := by
    rw [Nat.card_units, h.card_eq_sq]
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    zify [h1, Nat.one_le_pow 2 (2 ^ m) (by omega)]
    ring
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [hcard]; exact Dvd.dvd.mul_right h3 _)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hωN : h.norm (ω : K) = 1 := by
    obtain ⟨t, ht⟩ := h3
    rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, ht, pow_mul, hω3, one_pow,
      Units.val_one]
  have hmem := scalar_mem_unitarySU h (by norm_num : 1 ≤ 3) hωN hω3
  refine ⟨⟨_, hmem⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (commute_scalar ω (g : GL (Fin 3) K)).eq
  · intro h1
    have h2 : GeneralLinearGroup.scalar (Fin 3) ω = 1 := congrArg Subtype.val h1
    have h3' : ω = 1 := by
      have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h2
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Units.val_one, Matrix.one_apply_eq] at this
      exact Units.ext this
    rw [h3', orderOf_one] at hω
    omega
  · apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ← map_pow, hω3, map_one]
    rfl

theorem false_of_center_eq_bot_of_mulEquiv {X M : Type*} [Group X] [Group M] (e : X ≃* M)
    (hM : Subgroup.center M = ⊥) {z : X} (hz : z ∈ Subgroup.center X) (hz1 : z ≠ 1) : False := by
  have : e z ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz y']
  rw [hM, Subgroup.mem_bot] at this
  exact hz1 (e.injective (this.trans (map_one e).symm))

theorem false_of_isSimpleGroup_of_mulEquiv {X M : Type*} [Group X] [Group M] [IsSimpleGroup M]
    (e : X ≃* M) (hperf : Group.IsPerfect X) {z : X} (hz : z ∈ Subgroup.center X)
    (hz1 : z ≠ 1) : False := by
  have := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact hz1 hz
  · have hcomm : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top X).mpr h
    have htop : commutator X = ⊤ := hperf.commutator_eq_top
    have : z ∈ commutator X := by rw [htop]; exact Subgroup.mem_top z
    rw [hcomm, Subgroup.mem_bot] at this
    exact hz1 this

theorem center_unitaryPSU_three_eq_bot {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) : Subgroup.center (unitaryPSU h 3) = ⊥ := by
  have : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three h hq
  have hG := Group.IsPerfect.center_quotient_center_eq_bot (unitarySU p f K 3)
  rw [eq_bot_iff]
  intro z hz
  have e := suCenterEquiv h hq
  have : e.symm z ∈ Subgroup.center (unitarySU p f K 3 ⧸ Subgroup.center (unitarySU p f K 3)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz (e y)]
  rw [hG, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  have h1 := congrArg e this
  rwa [MulEquiv.apply_symm_apply, map_one] at h1

end Center

section Ident

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inducesKindSU3_of_inducesStdKind {m : ℕ} (hm : 3 ≤ m) (hm3 : 3 ∣ 2 ^ m + 1)
    (hL : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ m)) {x : G} {k : AutKind}
    (hx : InducesStdKind L x k) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 m K) (hq : 2 < 2 ^ m),
      InducesKindSU3 h L hq x k := by
  obtain ⟨K₀, _, _, hK₀, ⟨eL⟩⟩ := hL
  have h₀ : UnitaryFieldData 2 m K₀ := ⟨Nat.prime_two, by omega, by rw [hK₀, ← pow_mul,
    mul_comm]⟩
  have hQ8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq₀ : 2 < 2 ^ m := by omega
  obtain ⟨z₀, hz₀, hz₀1, hz₀3⟩ := exists_mem_center_statedSU_ne_one h₀ hm3
  set z : L ⧸ aschbacherSolvableCore 3 L := eL.symm z₀ with hzdef
  have hz : z ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff] at hz₀ ⊢
    intro y
    apply eL.injective
    rw [map_mul, map_mul, hzdef, MulEquiv.apply_symm_apply, hz₀ (eL y)]
  have hz1 : z ≠ 1 := fun h1 => hz₀1 (by rw [← eL.apply_symm_apply z₀, ← hzdef, h1, map_one])
  have hz3 : z ^ 3 = 1 := by rw [hzdef, ← map_pow, hz₀3, map_one]
  have : Group.IsPerfect (unitarySU 2 m K₀ 3) := isPerfect_unitarySU_three h₀ hq₀
  have hperf : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) :=
    Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hcardL : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
      (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) := by
    rw [Nat.card_congr eL.toEquiv]
    exact card_unitarySU_three h₀
  cases hx with
  | psl2 K h =>
    obtain ⟨e, -⟩ := h
    exact (false_of_center_eq_bot_of_mulEquiv e (CFSG.GorensteinWalter.psl2_center_eq_bot K)
      hz hz1).elim
  | psl n K hn h =>
    obtain ⟨e, -⟩ := h
    have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := n) (by omega)
      (Or.inl hn)).2.1
    have : IsSimpleGroup (LinearFlag.projectiveSL n K) :=
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        n K).symm.isSimpleGroup
    exact (false_of_isSimpleGroup_of_mulEquiv e hperf hz hz1).elim
  | sl n K hn h =>
    obtain ⟨e, -, -⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have hK3 : ringChar K ≠ 3 := by
      intro hc
      have : CharP K 3 := ringChar.of_eq hc
      have hez : e z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro y
        obtain ⟨y', rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul, hz y']
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hez
      have hez3 : (e z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
      have hr3 : r ^ 3 = 1 := by
        have h1 : (Matrix.scalar (Fin n) r) ^ 3 = 1 := by
          rw [hr, ← Matrix.SpecialLinearGroup.coe_pow, hez3, Matrix.SpecialLinearGroup.coe_one]
        rw [← map_pow] at h1
        have h2 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
        simpa [Matrix.scalar_apply] using h2
      have hr1 : r = 1 := by
        have h1 : (r - 1) ^ 3 = 0 := by
          have h2 : (3 : K) = 0 := CharP.cast_eq_zero K 3
          linear_combination hr3 + (r - r ^ 2) * h2
        have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h1
        exact sub_eq_zero.mp this
      apply hz1
      apply e.injective
      rw [map_one]
      apply Subtype.ext
      rw [← hr, hr1, map_one]
      rfl
    have h1 := card_SL_ne_su3Order (n := n) hn hK3 (Q := 2 ^ m) (m := m) rfl hQ8
    exact (h1 (by rw [← Nat.card_congr e.toEquiv, hcardL])).elim
  | psu3 hK hq h =>
    obtain ⟨e, -⟩ := h
    exact (false_of_center_eq_bot_of_mulEquiv e (center_unitaryPSU_three_eq_bot hK hq)
      hz hz1).elim
  | @su3 p f K _ hK hq h =>
    have hcard : Nat.card (unitarySU p f K 3) = (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)
        := by
      obtain ⟨e, -, -⟩ := h
      rw [← Nat.card_congr e.toEquiv, hcardL]
    rw [card_unitarySU_three hK] at hcard
    have hqq : p ^ f = 2 ^ m := su3Order_injective (Nat.one_le_pow _ _ hK.prime.pos)
      (Nat.one_le_two_pow) hcard
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp
      (hK.prime.dvd_of_dvd_pow (show p ∣ 2 ^ m from hqq ▸ dvd_pow_self p
        (by have := hK.one_le; omega)))
    subst hp2
    have hfm : f = m := Nat.pow_right_injective (le_refl 2) hqq
    subst hfm
    exact ⟨K, inferInstance, hK, hq, h⟩
  | psp r K hr h =>
    obtain ⟨e, -⟩ := h
    have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSp r K)) := by
      refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r
        (by rcases hr with hr | ⟨rfl, -⟩ <;> omega) ?_
      have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
      rcases Nat.lt_or_ge (Nat.card K) 4 with h4 | h4
      · rcases (by omega : Nat.card K = 2 ∨ Nat.card K = 3) with h2 | h3
        · right; right
          refine ⟨h2, ?_⟩
          rcases hr with hr | ⟨rfl, hc⟩
          · exact hr
          · exfalso
            apply hc
            have : Fintype K := Fintype.ofFinite K
            obtain ⟨p, hp⟩ := CharP.exists K
            have := hp
            obtain ⟨n, hpn, hn⟩ := FiniteField.card K p
            rw [← Nat.card_eq_fintype_card, h2] at hn
            have hp2 : p = 2 := by
              have := (Nat.prime_dvd_prime_iff_eq hpn Nat.prime_two).mp
                (hn ▸ dvd_pow_self p n.ne_zero)
              exact this
            rw [ringChar.eq K p, hp2]
        · right; left
          refine ⟨h3, ?_⟩
          rcases hr with hr | ⟨rfl, -⟩ <;> omega
      · exact Or.inl (Or.inr h4)
    exact (false_of_isSimpleGroup_of_mulEquiv e hperf hz hz1).elim
  | psp4even F h =>
    obtain ⟨e, -⟩ := h
    exact (false_of_center_eq_bot_of_mulEquiv e
      (CFSG.QuasithinUnique.Lin2.Five.center_statedProj_eq_bot F) hz hz1).elim
  | g2 K hK3 hK4 h =>
    obtain ⟨e, -⟩ := h
    exact (false_of_center_eq_bot_of_mulEquiv e CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
      hz hz1).elim
  | sz a K ha hK h =>
    obtain ⟨e, -⟩ := h
    have := Nat.finite_of_card_ne_zero (by rw [hK]; positivity : Nat.card K ≠ 0)
    obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
    exact (false_of_isSimpleGroup_of_mulEquiv e hperf hz hz1).elim
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, -, -⟩ := h
    exact (false_of_center_eq_bot_of_mulEquiv e
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective) hz hz1).elim
  | largeRee a ha K hK h =>
    obtain ⟨e, -⟩ := h
    exact (false_of_center_eq_bot_of_mulEquiv e
      (CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial a K hK) hz hz1).elim

theorem three_dvd_two_pow_three_mul_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ (3 * n) + 1 := by
  have h := Odd.nat_add_dvd_pow_add_pow 2 1 (Odd.mul (by decide : Odd 3) hn)
  simpa using h

theorem not_inducesStdKind_graphField_of_isoSUThree {m : ℕ} (hm : 3 ≤ m) (hm3 : 3 ∣ 2 ^ m + 1)
    (hL : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ m)) {x : G} :
    ¬ InducesStdKind L x .graphField := by
  intro hx
  obtain ⟨K, _, h, hq, e, hN, hk⟩ := inducesKindSU3_of_inducesStdKind hm hm3 hL hx
  obtain ⟨γ, hγ, -⟩ := hk
  exact hγ

theorem isoSUThree_barCentralizer_of_inducesStdKind {n : ℕ} (hn : Odd n)
    (hL : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n))) {a : G}
    (ha3 : a ^ 3 = 1) (ha : InducesStdKind L a .field) :
    Sec8.IsoSUThree (Sec8.barCentralizer (Subgroup.zpowers a) L) (2 ^ n) := by
  have hn1 : 1 ≤ n := hn.pos
  obtain ⟨K, _, h, hq, hk⟩ := inducesKindSU3_of_inducesStdKind (by omega)
    (three_dvd_two_pow_three_mul_add_one hn) hL ha
  obtain ⟨f₀, hf₀, hC⟩ := isoSUThree_barCentralizer_of_field hq ha3 hk
  obtain rfl : f₀ = n := by omega
  exact hC

end Ident

end CFSG.RankThree.PartTwo.KFacts

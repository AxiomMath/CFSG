module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open Matrix

section Orders

theorem sl3Order_lt {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) :
    x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) < y ^ 3 * (y ^ 2 - 1) * (y ^ 3 - 1) := by
  have hy : 2 ≤ y := by omega
  have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  have hx3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  have hxy2 : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left hxy (by norm_num)
  have hxy3 : x ^ 3 < y ^ 3 := Nat.pow_lt_pow_left hxy (by norm_num)
  have hy2 : 4 ≤ y ^ 2 := by nlinarith
  calc x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) ≤ y ^ 3 * (y ^ 2 - 1) * (x ^ 3 - 1) := by
        gcongr
    _ < y ^ 3 * (y ^ 2 - 1) * (y ^ 3 - 1) := by
        have : 0 < y ^ 3 * (y ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
        exact Nat.mul_lt_mul_of_pos_left (by omega) this

theorem pow_fifteen_le_sq_sl3Order {Q : ℕ} (hQ : 4 ≤ Q) :
    Q ^ 15 ≤ (Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1)) ^ 2 := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h3]
  have hQ' : (4 : ℤ) ≤ Q := by exact_mod_cast hQ
  have h0 : (0 : ℤ) < Q := by omega
  nlinarith [pow_pos h0 2, pow_pos h0 3, pow_pos h0 4, pow_pos h0 5, pow_pos h0 6, pow_pos h0 7,
    pow_pos h0 8, pow_pos h0 9, pow_pos h0 10, pow_pos h0 11, pow_pos h0 12, pow_pos h0 13,
    pow_pos h0 14, mul_le_mul_of_nonneg_left hQ' (pow_pos h0 14).le]

theorem lt_sl3Order {Q : ℕ} (hQ : 4 ≤ Q) : (Q + 1) ^ 6 < Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h3]
  have hQ' : (4 : ℤ) ≤ Q := by exact_mod_cast hQ
  have h0 : (0 : ℤ) < Q := by omega
  nlinarith [pow_pos h0 2, pow_pos h0 3, pow_pos h0 4, pow_pos h0 5, pow_pos h0 6, pow_pos h0 7,
    mul_le_mul_of_nonneg_left hQ' (pow_pos h0 7).le]

theorem sl3Order_factor {Q : ℕ} (hQ : 1 ≤ Q) :
    (Q ^ 2 - 1) * (Q ^ 3 - 1) = (Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1)) := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ
  zify [h2, h3, hQ]
  ring

theorem not_two_dvd_sl3OddPart {Q : ℕ} (hQ : 2 ≤ Q) (hQeven : 2 ∣ Q) :
    ¬ 2 ∣ (Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1)) := by
  obtain ⟨t, ht⟩ := hQeven
  have hQ2 : Q ^ 2 = 2 * (2 * t ^ 2) := by rw [ht]; ring
  rw [Nat.prime_two.dvd_mul, Nat.prime_two.dvd_mul]
  rintro (h | h | h)
  · omega
  · have := Nat.prime_two.dvd_of_dvd_pow h
    omega
  · omega

theorem le_of_prime_pow_dvd_sl3OddPart {ℓ v Q : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hQ : 2 ≤ Q) (h : ℓ ^ v ∣ (Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1))) :
    ℓ ^ v ≤ (Q + 1) ^ 2 := by
  have hcases := prime_pow_dvd_of_dvd_mul_three (v := v) hℓ
    (fun ⟨h1, h2⟩ => by
      have h2' := hℓ.dvd_of_dvd_pow h2
      have : ℓ ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub h1 h2'
      rw [show (Q + 1) - (Q - 1) = 2 by omega] at this
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this))
    (fun ⟨h1, h2⟩ => by
      have : ℓ ∣ (Q ^ 2 + Q + 1) - Q * (Q + 1) := Nat.dvd_sub h2 (Dvd.dvd.mul_left h1 Q)
      rw [show (Q ^ 2 + Q + 1) - Q * (Q + 1) = 1 by rw [sq]; ring_nf; omega] at this
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp this))
    (fun ⟨h1, h2⟩ => by
      have h1' := hℓ.dvd_of_dvd_pow h1
      have hid : (Q - 1) * (Q + 2) + 3 = Q ^ 2 + Q + 1 := by
        zify [(by omega : 1 ≤ Q)]
        ring
      have : ℓ ∣ (Q ^ 2 + Q + 1) - (Q - 1) * (Q + 2) :=
        Nat.dvd_sub h2 (Dvd.dvd.mul_right h1' (Q + 2))
      rw [show (Q ^ 2 + Q + 1) - (Q - 1) * (Q + 2) = 3 by omega] at this
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp this)) h
  have hsq : (Q + 1) ^ 2 = Q ^ 2 + 2 * Q + 1 := by ring
  have hQ1 : (Q - 1) ^ 2 ≤ (Q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  rcases hcases with h | h | h
  · exact (Nat.le_of_dvd (by omega) h).trans (by nlinarith)
  · exact (Nat.le_of_dvd (pow_pos (by omega) 2) h).trans hQ1
  · exact (Nat.le_of_dvd (by positivity) h).trans (by omega)

theorem eq_of_card_SL_eq_sl3Order {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Fintype K]
    (hK3 : ringChar K ≠ 3) {Q m : ℕ} (hQ : Q = 2 ^ m) (hQ8 : 8 ≤ Q)
    (heq : Nat.card (SpecialLinearGroup (Fin n) K) = Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1)) :
    n = 3 ∧ Fintype.card K = Q := by
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
  generalize Fintype.card K = k at hN0 hlt0 hlt1 h30 hk1 hk ⊢
  set e := n * (n - 1) / 2 with he
  have he2 : 2 * e = n * (n - 1) := by
    rw [he]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  have hN : k ^ e ∣ Q ^ 3 * ((Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1))) := by
    rw [← sl3Order_factor (by omega), ← mul_assoc]
    exact hN0
  have hkℓ : k ^ e = ℓ ^ ((b : ℕ) * e) := by rw [hk, ← pow_mul]
  have hodd := not_two_dvd_sl3OddPart (by omega) hQeven
  by_cases hℓ2 : ℓ = 2
  ·
    subst hℓ2
    have hcop : Nat.Coprime (k ^ e) ((Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1))) := by
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
      refine ⟨rfl, le_antisymm hkQ ?_⟩
      by_contra hlt
      push Not at hlt
      exact absurd h3 (ne_of_gt (sl3Order_lt (by omega) hlt))
    ·
      exfalso
      set S := Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) with hS
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
          _ ≤ (S ^ 2) ^ n := Nat.pow_le_pow_left (pow_fifteen_le_sq_sl3Order (by omega)) n
          _ = S ^ (2 * n) := by rw [← pow_mul]
      have h3 : S ^ (2 * n) < Q ^ (12 * (n + 1)) := by
        calc S ^ (2 * n) = (S ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
          _ < (Q ^ (6 * (n + 1))) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
          _ = Q ^ (12 * (n + 1)) := by rw [← pow_mul]; ring_nf
      have h4 : Q ^ (12 * (n + 1)) ≤ Q ^ (15 * n) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  ·
    exfalso
    have hℓ3 : ℓ ≠ 3 := fun h3 => hK3 (hringChar.trans h3)
    have hℓQ : ¬ ℓ ∣ Q := fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
      (hℓ.dvd_of_dvd_pow (hQ ▸ h)))
    have hcop : Nat.Coprime (k ^ e) (Q ^ 3) := by
      rw [hkℓ]
      exact Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓQ)
    have hN' : ℓ ^ ((b : ℕ) * e) ∣ (Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1)) := by
      rw [← hkℓ]
      exact hcop.dvd_of_dvd_mul_left hN
    have hle : k ^ e ≤ (Q + 1) ^ 2 := by
      rw [hkℓ]
      exact le_of_prime_pow_dvd_sl3OddPart hℓ hℓ2 hℓ3 (by omega) hN'
    have hexp : n ^ 2 ≤ 3 * e := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
      have h2 : 2 * e = (n' + 3) * (n' + 2) := by
        rw [he2, show n' + 3 - 1 = n' + 2 by omega]
      nlinarith
    have h1 : Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) < (Q + 1) ^ 6 := by
      calc Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) < k ^ (n ^ 2) := hlt0
        _ ≤ k ^ (3 * e) := Nat.pow_le_pow_right (by omega) hexp
        _ = (k ^ e) ^ 3 := by rw [← pow_mul, mul_comm]
        _ ≤ ((Q + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hle 3
        _ = (Q + 1) ^ 6 := by rw [← pow_mul]
    have h2 := lt_sl3Order (Q := Q) (by omega)
    omega

theorem su3Order_ne_sl3Order {p f Q m : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hQ : Q = 2 ^ m) (hQ8 : 8 ≤ Q) :
    (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) ≠ Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) := by
  intro heq
  set x := p ^ f with hx
  have hx2 : 2 ≤ x := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [hQ, h0] at hQ8; norm_num at hQ8
    · exact h0
  have hQeven : 2 ∣ Q := by rw [hQ]; exact dvd_pow_self 2 (by omega)
  have hfac : Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) =
      Q ^ 3 * ((Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1))) := by
    rw [mul_assoc, sl3Order_factor (by omega)]
  have hodd := not_two_dvd_sl3OddPart (by omega) hQeven
  have hx3 : x ^ 3 ∣ Q ^ 3 * ((Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1))) := by
    rw [← hfac, ← heq, mul_assoc]
    exact Dvd.intro _ rfl
  by_cases hp2 : p = 2
  ·
    have hxQ : x ^ 3 ∣ Q ^ 3 := by
      have hcop : Nat.Coprime (x ^ 3) ((Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1))) := by
        rw [hx, hp2, ← pow_mul]
        exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
      exact hcop.dvd_of_dvd_mul_right hx3
    have hxodd : ¬ 2 ∣ (x ^ 2 - 1) * (x ^ 3 + 1) := by
      have hxeven : 2 ∣ x := by rw [hx, hp2]; exact dvd_pow_self 2 (by omega)
      obtain ⟨t, ht⟩ := hxeven
      have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
      have hx2' : x ^ 2 = 2 * (2 * t ^ 2) := by rw [ht]; ring
      have hx3' : x ^ 3 = 2 * (4 * t ^ 3) := by rw [ht]; ring
      rw [Nat.prime_two.dvd_mul]
      rintro (h | h) <;> omega
    have hQx : Q ^ 3 ∣ x ^ 3 := by
      have hcop : Nat.Coprime (Q ^ 3) ((x ^ 2 - 1) * (x ^ 3 + 1)) := by
        rw [hQ, ← pow_mul]
        exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hxodd)
      refine hcop.dvd_of_dvd_mul_right ?_
      rw [← mul_assoc, heq, mul_assoc]
      exact Dvd.intro _ rfl
    have hxQ' : x = Q := Nat.pow_left_injective (by norm_num : 3 ≠ 0)
      (Nat.dvd_antisymm hxQ hQx)
    rw [hxQ'] at heq
    have hpos : 0 < Q ^ 3 * (Q ^ 2 - 1) := by
      have : 1 < Q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
      have : 0 < Q ^ 2 - 1 := by omega
      positivity
    have := Nat.eq_of_mul_eq_mul_left hpos heq
    omega
  ·
    have hcop : Nat.Coprime (x ^ 3) (Q ^ 3) := by
      rw [hx, hQ, ← pow_mul, ← pow_mul]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hdvd : p ^ (f * 3) ∣ (Q + 1) * ((Q - 1) ^ 2 * (Q ^ 2 + Q + 1)) := by
      rw [pow_mul, ← hx]
      exact hcop.dvd_of_dvd_mul_left hx3
    have hle := le_of_prime_pow_dvd_sl3OddPart hp hp2 hp3 (by omega) hdvd
    rw [pow_mul, ← hx] at hle
    have hlt : x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) < (x ^ 3) ^ 3 := by
      have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h4 : x ^ 3 + 1 ≤ x ^ 4 := by
        have : x ^ 4 = x ^ 3 * x := by ring
        nlinarith [Nat.one_le_pow 3 x (by omega)]
      calc x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) < x ^ 3 * x ^ 2 * x ^ 4 := by
            have : x ^ 2 - 1 < x ^ 2 := by omega
            have h3 : 0 < x ^ 3 := by positivity
            calc x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) ≤ x ^ 3 * (x ^ 2 - 1) * x ^ 4 := by gcongr
              _ < x ^ 3 * x ^ 2 * x ^ 4 := by
                  apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
                  exact Nat.mul_lt_mul_of_pos_left this h3
        _ = (x ^ 3) ^ 3 := by ring
    have h6 : (x ^ 3) ^ 3 ≤ (Q + 1) ^ 6 :=
      calc (x ^ 3) ^ 3 ≤ ((Q + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hle 3
        _ = (Q + 1) ^ 6 := by ring
    exact (ne_of_lt ((lt_of_lt_of_le hlt h6).trans (lt_sl3Order (by omega)))) heq

end Orders

section Ident

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inducesKindSL_of_inducesStdKind {m : ℕ} (hm : 3 ≤ m) (hm3 : 2 ^ m % 3 = 1)
    (hL : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K))
    {x : G} {k : AutKind} (hx : InducesStdKind L x k) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧ InducesKindSL 3 K L x k := by
  obtain ⟨K₀, _, _, hK₀, ⟨eL₀⟩⟩ := hL
  set eL : L ⧸ aschbacherSolvableCore 3 L ≃* slPi true 3 (2 ^ m) K₀ := eL₀ with heL
  have hQ8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hPi : PiField true 2 m K₀ := ⟨Nat.prime_two, by omega, hK₀⟩
  have hmod : ModThree true (2 ^ m) := hm3
  have hc3 := card_center_slPi hPi hmod
  obtain ⟨z₀, hz₀1⟩ : ∃ z₀ : Subgroup.center (slPi true 3 (2 ^ m) K₀), z₀ ≠ 1 := by
    have : Nontrivial (Subgroup.center (slPi true 3 (2 ^ m) K₀)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hc3]; norm_num)
    exact exists_ne 1
  obtain ⟨ζ, hζ3, hζz⟩ := exists_scalar_of_mem_center hPi hmod z₀.2
  set z : L ⧸ aschbacherSolvableCore 3 L := eL.symm (z₀ : slPi true 3 (2 ^ m) K₀) with hzdef
  have hz : z ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) :=
    mem_center_of_mulEquiv eL.symm z₀.2
  have hz1 : z ≠ 1 := fun h => hz₀1 (Subtype.ext (eL.symm.injective (h.trans (map_one _).symm)))
  have hz3 : z ^ 3 = 1 := by
    have h1 : (z₀ : slPi true 3 (2 ^ m) K₀) ^ 3 = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hζz, ← map_pow, hζ3, map_one]
      rfl
    rw [hzdef, ← map_pow, h1, map_one]
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) K₀) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have hperf : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) :=
    Group.IsPerfect.ofSurjective (f := (eL.trans (slPiTrueEquiv (2 ^ m) K₀)).symm.toMonoidHom)
      (eL.trans (slPiTrueEquiv (2 ^ m) K₀)).symm.surjective
  have hcardL : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
      (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) := by
    have : Fintype K₀ := Fintype.ofFinite K₀
    rw [Nat.card_congr (eL.trans (slPiTrueEquiv (2 ^ m) K₀)).toEquiv, card_SL_three,
      ← Nat.card_eq_fintype_card, hK₀]
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
    obtain ⟨e, hxN, hk⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have hK3 : ringChar K ≠ 3 := by
      intro hc
      have : CharP K 3 := ringChar.of_eq hc
      have hez : e z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
        mem_center_of_mulEquiv e hz
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
    obtain ⟨rfl, hcardK⟩ := eq_of_card_SL_eq_sl3Order hn hK3 (Q := 2 ^ m) (m := m) rfl hQ8
      (by rw [← Nat.card_congr e.toEquiv, hcardL])
    exact ⟨K, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hcardK],
      ⟨e, hxN, hk⟩⟩
  | psu3 hK hq h =>
    obtain ⟨e, -⟩ := h
    exact (false_of_center_eq_bot_of_mulEquiv e (center_unitaryPSU_three_eq_bot hK hq)
      hz hz1).elim
  | @su3 p f K _ hK hq h =>
    obtain ⟨e, -, -⟩ := h
    have hp3 : p ≠ 3 := by
      rintro rfl
      have : CharP K 3 := hK.charP
      have hbot : Subgroup.center (unitarySU 3 f K 3) = ⊥ := by
        rw [center_unitarySU_three (h := hK) hq, eq_bot_iff]
        rintro g ⟨c, -, hc3, hg⟩
        have hc1 : c = 1 := by
          have hc3' : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
          have h1 : ((c : K) - 1) ^ 3 = 0 := by
            have h2 : (3 : K) = 0 := CharP.cast_eq_zero K 3
            linear_combination hc3' + ((c : K) - (c : K) ^ 2) * h2
          exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h1))
        rw [Subgroup.mem_bot]
        apply Subtype.ext
        rw [hg, hc1, map_one]
        rfl
      exact false_of_center_eq_bot_of_mulEquiv e hbot hz hz1
    have hcard : Nat.card (unitarySU p f K 3) =
        (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) := by
      rw [← Nat.card_congr e.toEquiv, hcardL]
    rw [card_unitarySU_three hK] at hcard
    exact (su3Order_ne_sl3Order hK.prime hp3 hK.one_le rfl hQ8 hcard).elim
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

theorem not_inducesStdKind_graphField_of_isoSLThree {m : ℕ} (hm : 3 ≤ m) (hm3 : 2 ^ m % 3 = 1)
    (hL : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K))
    {x : G} (hx3 : x ^ 3 = 1) : ¬ InducesStdKind L x .graphField := by
  intro hx
  obtain ⟨K, _, _, -, e, hxN, hk⟩ := inducesKindSL_of_inducesStdKind hm hm3 hL hx
  have hsep := stdPinnedPSL_separated (K := K) (n := 3) le_rfl
  have hτ3 : LinearFlag.descendAut 3 K (inducedAutHom L e ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← map_pow, inducedAutHom_pow_eq_one L e hxN hx3, map_one]
  have hD := hsep.not_mem_inndiag_of_hasKind hk (by decide) (by decide)
  exact hsep.not_isGraphField_of_isField (isField_of_pow_three_eq_one le_rfl hτ3 hD)
    ((stdPinnedPSL 3 K).hasKind_graphField.mp hk)

end Ident

end CFSG.RankThree.PartTwo.KFacts

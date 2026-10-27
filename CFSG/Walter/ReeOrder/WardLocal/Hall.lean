module

public import CFSG.Walter.ReeOrder.WardLocal.CY

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct
open CFSG.BlockSectionOrthogonality.Helpers

section Arith

theorem hall_le {q m : ℕ} (hm : q = 3 * m ^ 2) : 3 * m ≤ q + 1 := by
  rw [hm]
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · nlinarith

theorem hall_mul {q m : ℕ} (hm : q = 3 * m ^ 2) :
    q ^ 2 - q + 1 = (q + 1 + 3 * m) * (q + 1 - 3 * m) := by
  have h1 := hall_le hm
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  zify [h1, h2]
  have hm' : (q : ℤ) = 3 * (m : ℤ) ^ 2 := by exact_mod_cast hm
  rw [hm']
  ring

theorem hall_coprime {q m : ℕ} (hm : q = 3 * m ^ 2) (hmodd : Odd m) :
    Nat.Coprime ((q + 1 - 3 * m) * (q + 1 + 3 * m)) q ∧
    Nat.Coprime ((q + 1 - 3 * m) * (q + 1 + 3 * m)) (q - 1) ∧
    Nat.Coprime ((q + 1 - 3 * m) * (q + 1 + 3 * m)) (q + 1) ∧
    Nat.Coprime ((q + 1 - 3 * m) * (q + 1 + 3 * m)) 2 ∧
    Nat.Coprime (q + 1 - 3 * m) (q + 1 + 3 * m) ∧ Nat.Coprime (q ^ 2 + 1) q := by
  obtain ⟨j, rfl⟩ := hmodd
  have h1 := hall_le hm
  have hq1 : 1 ≤ q := by rw [hm]; nlinarith
  have hmz : (q : ℤ) = 3 * (2 * (j : ℤ) + 1) ^ 2 := by rw [hm]; push_cast; ring
  have hN : ∀ y : ℕ, IsCoprime (((q + 1 - 3 * (2 * j + 1)) * (q + 1 + 3 * (2 * j + 1)) : ℕ) : ℤ)
      (y : ℤ) → Nat.Coprime ((q + 1 - 3 * (2 * j + 1)) * (q + 1 + 3 * (2 * j + 1))) y :=
    fun y h => Nat.isCoprime_iff_coprime.mp h
  have hab : (((q + 1 - 3 * (2 * j + 1)) * (q + 1 + 3 * (2 * j + 1)) : ℕ) : ℤ) =
      (q : ℤ) ^ 2 - q + 1 := by
    push_cast [h1]; rw [hmz]; ring
  refine ⟨hN q ?_, hN (q - 1) ?_, hN (q + 1) ?_, hN 2 ?_, ?_, ?_⟩
  · rw [hab]; exact ⟨1, -((q : ℤ) - 1), by ring⟩
  · rw [hab]; push_cast [hq1]; exact ⟨1, -(q : ℤ), by ring⟩
  · rw [hab]; push_cast
    refine ⟨-(2 * (j : ℤ) + 1) ^ 2, 1 + (2 * (j : ℤ) + 1) ^ 2 * ((q : ℤ) - 2), ?_⟩
    rw [hmz]; ring
  · rw [hab]; push_cast
    refine ⟨1, -((q : ℤ) * (6 * (j : ℤ) ^ 2 + 6 * j + 1)), ?_⟩
    rw [hmz]; ring
  · apply Nat.isCoprime_iff_coprime.mp
    push_cast [h1]
    have ha2 : IsCoprime ((q : ℤ) + 1 - 3 * (2 * j + 1)) 2 :=
      ⟨1, -(6 * (j : ℤ) ^ 2 + 3 * j), by rw [hmz]; ring⟩
    have haq : IsCoprime ((q : ℤ) + 1 - 3 * (2 * j + 1)) ((q : ℤ) + 1) := by
      refine ⟨-(2 * (j : ℤ) + 1) ^ 2 * ((q : ℤ) + 1 + 3 * (2 * j + 1)),
        1 + (2 * (j : ℤ) + 1) ^ 2 * ((q : ℤ) - 2), ?_⟩
      rw [hmz]; ring
    have h2 := ha2.mul_right haq
    apply IsCoprime.of_add_mul_left_right (z := 1)
    convert h2 using 1
    ring
  · apply Nat.isCoprime_iff_coprime.mp
    push_cast
    exact ⟨1, -(q : ℤ), by ring⟩

theorem ordProj_dvd_of_not_dvd {a K p : ℕ} (ha : 0 < a) (hK : 0 < K) (hpK : ¬ p ∣ K) :
    p ^ (a * K).factorization p ∣ a := by
  rw [Nat.factorization_mul ha.ne' hK.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpK, add_zero]
  exact Nat.ordProj_dvd a p


theorem jj_alg_minus {q m D D' N : ℂ} (hqm : q = 3 * m ^ 2) (hm : m ≠ 0)
    (h1 : 3 * m ^ 2 - 1 ≠ 0) (h2 : 3 * m ^ 2 + 1 ≠ 0) (hb : 3 * m ^ 2 + 1 + 3 * m ≠ 0)
    (hD : 2 * D = (q - 1) * m * (q + 1 + 3 * m)) (hD' : D' ≠ 0)
    (hN : N * (q * (q ^ 2 - 1)) * (q * (q ^ 2 - 1)) = q ^ 3 * (q ^ 3 + 1) * (q - 1) *
      (1 - 1 / q + (q - 1) ^ 2 * -1 / (2 * D) + (q - 1) ^ 2 * 0 / (2 * D'))) :
    N = q + 1 - 3 * m := by
  have eD : D = (q - 1) * m * (q + 1 + 3 * m) / 2 := by linear_combination hD / 2
  rw [eD, hqm] at hN
  rw [hqm]
  have hc : 3 * m ^ 2 * ((3 * m ^ 2) ^ 2 - 1) ≠ 0 := by
    have : (3 * m ^ 2) ^ 2 - 1 = (3 * m ^ 2 - 1) * (3 * m ^ 2 + 1) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hm)) (mul_ne_zero h1 h2)
  apply mul_right_cancel₀ (mul_ne_zero hc hc)
  rw [← mul_assoc, hN]
  field_simp
  ring

theorem jj_alg_plus {q m D D' N : ℂ} (hqm : q = 3 * m ^ 2) (hm : m ≠ 0)
    (h1 : 3 * m ^ 2 - 1 ≠ 0) (h2 : 3 * m ^ 2 + 1 ≠ 0) (ha : 3 * m ^ 2 + 1 - 3 * m ≠ 0)
    (hD : 2 * D = (q - 1) * m * (q + 1 - 3 * m)) (hD' : D' ≠ 0)
    (hN : N * (q * (q ^ 2 - 1)) * (q * (q ^ 2 - 1)) = q ^ 3 * (q ^ 3 + 1) * (q - 1) *
      (1 - 1 / q + (q - 1) ^ 2 * 0 / (2 * D') + (q - 1) ^ 2 * 1 / (2 * D))) :
    N = q + 1 + 3 * m := by
  have eD : D = (q - 1) * m * (q + 1 - 3 * m) / 2 := by linear_combination hD / 2
  rw [eD, hqm] at hN
  rw [hqm]
  have hc : 3 * m ^ 2 * ((3 * m ^ 2) ^ 2 - 1) ≠ 0 := by
    have : (3 * m ^ 2) ^ 2 - 1 = (3 * m ^ 2 - 1) * (3 * m ^ 2 + 1) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hm)) (mul_ne_zero h1 h2)
  apply mul_right_cancel₀ (mul_ne_zero hc hc)
  rw [← mul_assoc, hN]
  field_simp
  ring

end Arith

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

omit [CharP K 3] in
include hq in
theorem m_eq (hm : q = 3 * m ^ 2) : m = 3 ^ k := by
  have h1 : m ^ 2 = (3 ^ k) ^ 2 := by
    have : 3 * m ^ 2 = 3 * (3 ^ k) ^ 2 := by rw [← hm, hq, ← pow_mul, pow_succ']; ring_nf
    omega
  exact Nat.pow_left_injective (by norm_num) h1

omit [CharP K 3] in
include hq in
theorem m_odd (hm : q = 3 * m ^ 2) : Odd m := by
  rw [m_eq hq hm]; exact Odd.pow (by decide)

omit [Group G] [Fintype G] [CharP K 3] in
include hq hG in
theorem card_G_hall (hm : q = 3 * m ^ 2) :
    Nat.card G = (q + 1 - 3 * m) * (q ^ 3 * (q - 1) * (q + 1) * (q + 1 + 3 * m)) := by
  have h1 := hall_le hm
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  rw [hG]
  zify [h1, h2, hq1]
  have hm' : (q : ℤ) = 3 * (m : ℤ) ^ 2 := by exact_mod_cast hm
  rw [hm']
  ring

omit [CharP K 3] in
include hq in
theorem prime_minus (hm : q = 3 * m ^ 2) {p : ℕ} (hp : p.Prime) (hpa : p ∣ q + 1 - 3 * m) :
    ¬ p ∣ q ∧ ¬ p ∣ q - 1 ∧ ¬ p ∣ q + 1 ∧ ¬ p ∣ q + 1 + 3 * m ∧ p ≠ 2 := by
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := hall_coprime hm (m_odd hq hm)
  have hN : p ∣ (q + 1 - 3 * m) * (q + 1 + 3 * m) := dvd_mul_of_dvd_left hpa _
  have hnot : ∀ {y : ℕ}, Nat.Coprime ((q + 1 - 3 * m) * (q + 1 + 3 * m)) y → ¬ p ∣ y :=
    fun hc hy => hp.one_lt.ne' (Nat.dvd_one.mp (by
      rw [← Nat.Coprime.gcd_eq_one hc]; exact Nat.dvd_gcd hN hy))
  refine ⟨hnot c1, hnot c2, hnot c3, fun h => ?_, fun h => hnot c4 (by subst h; exact dvd_refl 2)⟩
  exact hp.one_lt.ne' (Nat.dvd_one.mp (by
    rw [← Nat.Coprime.gcd_eq_one c5]; exact Nat.dvd_gcd hpa h))

omit [CharP K 3] in
include hq in
theorem prime_plus (hm : q = 3 * m ^ 2) {p : ℕ} (hp : p.Prime) (hpb : p ∣ q + 1 + 3 * m) :
    ¬ p ∣ q ∧ ¬ p ∣ q - 1 ∧ ¬ p ∣ q + 1 ∧ ¬ p ∣ q + 1 - 3 * m ∧ p ≠ 2 := by
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := hall_coprime hm (m_odd hq hm)
  have hN : p ∣ (q + 1 - 3 * m) * (q + 1 + 3 * m) := dvd_mul_of_dvd_right hpb _
  have hnot : ∀ {y : ℕ}, Nat.Coprime ((q + 1 - 3 * m) * (q + 1 + 3 * m)) y → ¬ p ∣ y :=
    fun hc hy => hp.one_lt.ne' (Nat.dvd_one.mp (by
      rw [← Nat.Coprime.gcd_eq_one hc]; exact Nat.dvd_gcd hN hy))
  refine ⟨hnot c1, hnot c2, hnot c3, fun h => ?_, fun h => hnot c4 (by subst h; exact dvd_refl 2)⟩
  exact hp.one_lt.ne' (Nat.dvd_one.mp (by
    rw [← Nat.Coprime.gcd_eq_one c5]; exact Nat.dvd_gcd h hpb))

omit [Group G] [Fintype G] [CharP K 3] in
include hq hG in
theorem ppart_minus (hm : q = 3 * m ^ 2) {p : ℕ} (hp : p.Prime) (hpa : p ∣ q + 1 - 3 * m) :
    p ^ (Nat.card G).factorization p ∣ q + 1 - 3 * m := by
  obtain ⟨h1, h2, h3, h4, -⟩ := prime_minus hq hm hp hpa
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm; omega
    · exact h
  rw [card_G_hall hq hG hm]
  refine ordProj_dvd_of_not_dvd ?_ ?_ ?_
  · have : 3 * m < q + 1 := by rw [hm]; nlinarith
    omega
  · have : 0 < q - 1 := by omega
    positivity
  · intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact h1 (hp.dvd_of_dvd_pow h)
        · exact h2 h
      · exact h3 h
    · exact h4 h

omit [Group G] [Fintype G] [CharP K 3] in
include hq hG in
theorem ppart_plus (hm : q = 3 * m ^ 2) {p : ℕ} (hp : p.Prime) (hpb : p ∣ q + 1 + 3 * m) :
    p ^ (Nat.card G).factorization p ∣ q + 1 + 3 * m := by
  obtain ⟨h1, h2, h3, h4, -⟩ := prime_plus hq hm hp hpb
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm; omega
    · exact h
  have hcard : Nat.card G = (q + 1 + 3 * m) * (q ^ 3 * (q - 1) * (q + 1) * (q + 1 - 3 * m)) := by
    rw [card_G_hall hq hG hm]; ring
  rw [hcard]
  refine ordProj_dvd_of_not_dvd (by omega) ?_ ?_
  · have : 0 < q - 1 := by omega
    have : 3 * m < q + 1 := by rw [hm]; nlinarith
    have : 0 < q + 1 - 3 * m := by omega
    positivity
  · intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact h1 (hp.dvd_of_dvd_pow h)
        · exact h2 h
      · exact h3 h
    · exact h4 h

omit [CharP K 3] in
include B in
theorem deg_eta (i : S.W.RFam) : deg (D.η i) = (q : ℤ) ^ 3 + 1 := by
  rw [← B.dη_eq]
  have h1 := D.η_one i
  have h2 := deg_eq (D.mem i)
  rw [h1] at h2
  exact_mod_cast h2

omit [CharP K 3] in
include B in
theorem deg_eta' (i : S.W.RFam) : deg (D.η' i) = (q : ℤ) ^ 3 + 1 := by
  rw [← B.dη_eq]
  have h1 := D.η'_one i
  have h2 := deg_eq (D.mem' i)
  rw [h1] at h2
  exact_mod_cast h2

omit [CharP K 3] in
include hq hG in
theorem deg_orbit (O : S.Orbit) {χ : G → ℂ} (hχ : χ ∈ O.R) :
    deg χ = ((q : ℤ) - 1) * ((q : ℤ) ^ 2 - q + 1) := by
  rw [(O.deg_const hχ).1]
  have hc := O.card_G
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  rw [hG] at hc
  push_cast [hq1] at hc
  have h0 : (q : ℤ) ^ 3 * ((q : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ h0
  linear_combination -hc

theorem isCoprime_two_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (v : ℕ) :
    IsCoprime ((p ^ v : ℕ) : ℤ) 2 := by
  have h : Nat.Coprime (p ^ v) 2 :=
    Nat.Coprime.pow_left v ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact_mod_cast Nat.isCoprime_iff_coprime.mpr h

omit [CharP K 3] in
include B hq hG in
theorem van_minus (hm : q = 3 * m ^ 2) {x : G} {p : ℕ} (hp : p.Prime)
    (hpa : p ∣ q + 1 - 3 * m) (hpx : p ∣ orderOf x) :
    B.ξ₂ x = 0 ∧ B.ξ₄ x = 0 ∧ B.ξ₆ x = 0 ∧ (∀ i, D.η i x = 0) ∧ (∀ i, D.η' i x = 0) ∧
      ∀ O : S.Orbit, ∀ χ ∈ O.R, χ x = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpp := ppart_minus hq hG hm hp hpa
  have hle := hall_le hm
  have hm' : (q : ℤ) = 3 * (m : ℤ) ^ 2 := by exact_mod_cast hm
  have hab : ((q : ℤ) ^ 2 - q + 1) = ((q + 1 - 3 * m : ℕ) : ℤ) * ((q : ℤ) + 1 + 3 * m) := by
    push_cast [hle]; rw [hm']; ring
  have hdvdN : ((p ^ (Nat.card G).factorization p : ℕ) : ℤ) ∣ (q : ℤ) ^ 2 - q + 1 := by
    rw [hab]; exact Dvd.dvd.mul_right (by exact_mod_cast hpp) _
  have hq3 : (q : ℤ) ^ 3 + 1 = ((q : ℤ) + 1) * ((q : ℤ) ^ 2 - q + 1) := by ring
  refine ⟨defect_zero_vanish B.irr_2 p (by rw [B.deg_2]; exact hdvdN) hpx,
    defect_zero_vanish B.irr_4 p (by rw [B.deg_4]; exact Dvd.dvd.mul_left hdvdN _) hpx,
    defect_zero_vanish B.irr_6 p ?_ hpx,
    fun i => defect_zero_vanish (D.mem i) p
      (by rw [B.deg_eta i, hq3]; exact Dvd.dvd.mul_left hdvdN _) hpx,
    fun i => defect_zero_vanish (D.mem' i) p
      (by rw [B.deg_eta' i, hq3]; exact Dvd.dvd.mul_left hdvdN _) hpx,
    fun O χ hχ => defect_zero_vanish (O.R_mem hχ) p
      (by rw [deg_orbit hq hG O hχ]; exact Dvd.dvd.mul_left hdvdN _) hpx⟩
  have hd : ((p ^ (Nat.card G).factorization p : ℕ) : ℤ) ∣ 2 * deg B.ξ₆ := by
    rw [B.deg_6]
    have : ((q : ℤ) - 1) * m * (q + 1 - 3 * m) = ((q : ℤ) - 1) * m * ((q + 1 - 3 * m : ℕ) : ℤ) := by
      push_cast [hle]; ring
    rw [this]
    exact Dvd.dvd.mul_left (by exact_mod_cast hpp) _
  exact (isCoprime_two_of_prime hp (prime_minus hq hm hp hpa).2.2.2.2 _).dvd_of_dvd_mul_left hd

omit [CharP K 3] in
include B hq hG in
theorem van_plus (hm : q = 3 * m ^ 2) {x : G} {p : ℕ} (hp : p.Prime)
    (hpb : p ∣ q + 1 + 3 * m) (hpx : p ∣ orderOf x) :
    B.ξ₂ x = 0 ∧ B.ξ₄ x = 0 ∧ B.ξ₅ x = 0 ∧ (∀ i, D.η i x = 0) ∧ (∀ i, D.η' i x = 0) ∧
      ∀ O : S.Orbit, ∀ χ ∈ O.R, χ x = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpp := ppart_plus hq hG hm hp hpb
  have hle := hall_le hm
  have hm' : (q : ℤ) = 3 * (m : ℤ) ^ 2 := by exact_mod_cast hm
  have hab : ((q : ℤ) ^ 2 - q + 1) = ((q + 1 + 3 * m : ℕ) : ℤ) * ((q : ℤ) + 1 - 3 * m) := by
    push_cast; rw [hm']; ring
  have hdvdN : ((p ^ (Nat.card G).factorization p : ℕ) : ℤ) ∣ (q : ℤ) ^ 2 - q + 1 := by
    rw [hab]; exact Dvd.dvd.mul_right (by exact_mod_cast hpp) _
  have hq3 : (q : ℤ) ^ 3 + 1 = ((q : ℤ) + 1) * ((q : ℤ) ^ 2 - q + 1) := by ring
  refine ⟨defect_zero_vanish B.irr_2 p (by rw [B.deg_2]; exact hdvdN) hpx,
    defect_zero_vanish B.irr_4 p (by rw [B.deg_4]; exact Dvd.dvd.mul_left hdvdN _) hpx,
    defect_zero_vanish B.irr_5 p ?_ hpx,
    fun i => defect_zero_vanish (D.mem i) p
      (by rw [B.deg_eta i, hq3]; exact Dvd.dvd.mul_left hdvdN _) hpx,
    fun i => defect_zero_vanish (D.mem' i) p
      (by rw [B.deg_eta' i, hq3]; exact Dvd.dvd.mul_left hdvdN _) hpx,
    fun O χ hχ => defect_zero_vanish (O.R_mem hχ) p
      (by rw [deg_orbit hq hG O hχ]; exact Dvd.dvd.mul_left hdvdN _) hpx⟩
  have hd : ((p ^ (Nat.card G).factorization p : ℕ) : ℤ) ∣ 2 * deg B.ξ₅ := by
    rw [B.deg_5]
    have : ((q : ℤ) - 1) * m * (q + 1 + 3 * m) = ((q : ℤ) - 1) * m * ((q + 1 + 3 * m : ℕ) : ℤ) := by
      push_cast; ring
    rw [this]
    exact Dvd.dvd.mul_left (by exact_mod_cast hpp) _
  exact (isCoprime_two_of_prime hp (prime_plus hq hm hp hpb).2.2.2.2 _).dvd_of_dvd_mul_left hd

omit [CharP K 3] in
include B hq hG in
theorem val_minus (hm : q = 3 * m ^ 2) {x : G} (hx : Odd (orderOf x)) {p : ℕ} (hp : p.Prime)
    (hpa : p ∣ q + 1 - 3 * m) (hpx : p ∣ orderOf x) : B.ξ₃ x = -1 ∧ B.ξ₅ x = -1 := by
  obtain ⟨h2, h4, h6, -⟩ := B.van_minus hq hG hm hp hpa hpx
  have hd1 := B.col_d1 hx
  have hd2 := B.col_d2 hx
  rw [h2, h4] at hd1
  have h3 : B.ξ₃ x = -1 := by linear_combination hd1
  refine ⟨h3, ?_⟩
  rw [h3, h4, h6] at hd2
  linear_combination -hd2

omit [CharP K 3] in
include B hq hG in
theorem val_plus (hm : q = 3 * m ^ 2) {x : G} (hx : Odd (orderOf x)) {p : ℕ} (hp : p.Prime)
    (hpb : p ∣ q + 1 + 3 * m) (hpx : p ∣ orderOf x) : B.ξ₃ x = -1 ∧ B.ξ₆ x = 1 := by
  obtain ⟨h2, h4, h5, -⟩ := B.van_plus hq hG hm hp hpb hpx
  have hd1 := B.col_d1 hx
  have hd2 := B.col_d2 hx
  rw [h2, h4] at hd1
  have h3 : B.ξ₃ x = -1 := by linear_combination hd1
  refine ⟨h3, ?_⟩
  rw [h3, h4, h5] at hd2
  linear_combination hd2

omit [CharP K 3] in
theorem c5_S1 : starRingEnd ℂ ∘ B.ξ₅ ∉ S.S1 := by
  rw [B.hS1]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨fun h => S.one_not_S3 (h ▸ B.conj5_S3), fun h => B.ξ₂_S3 (h ▸ B.conj5_S3),
    fun h => B.n3c5 h.symm, fun h => B.n4c5 h.symm⟩

omit [CharP K 3] in
theorem c6_S1 : starRingEnd ℂ ∘ B.ξ₆ ∉ S.S1 := by
  rw [B.hS1]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨fun h => S.one_not_S3 (h ▸ B.conj6_S3), fun h => B.ξ₂_S3 (h ▸ B.conj6_S3),
    fun h => B.n3c6 h.symm, fun h => B.n4c6 h.symm⟩

omit [CharP K 3] in
theorem c5_S2 : starRingEnd ℂ ∘ B.ξ₅ ∉ S.S2 := by
  rw [B.hS2]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨fun h => B.n3c5 h.symm, fun h => B.n4c5 h.symm, fun h => B.ξ₅_S3 (h ▸ B.conj5_S3),
    fun h => B.ξ₆_S3 (h ▸ B.conj5_S3)⟩

omit [CharP K 3] in
theorem c6_S2 : starRingEnd ℂ ∘ B.ξ₆ ∉ S.S2 := by
  rw [B.hS2]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨fun h => B.n3c6 h.symm, fun h => B.n4c6 h.symm, fun h => B.ξ₅_S3 (h ▸ B.conj6_S3),
    fun h => B.ξ₆_S3 (h ▸ B.conj6_S3)⟩

omit [CharP K 3] in
theorem d_zero : S.d2 B.ξ₂ = 0 ∧ S.d3 B.ξ₂ = 0 ∧ S.d1 B.ξ₅ = 0 ∧ S.d3 B.ξ₅ = 0 ∧
    S.d1 B.ξ₆ = 0 ∧ S.d3 B.ξ₆ = 0 ∧ S.d1 (starRingEnd ℂ ∘ B.ξ₅) = 0 ∧
    S.d2 (starRingEnd ℂ ∘ B.ξ₅) = 0 ∧ S.d1 (starRingEnd ℂ ∘ B.ξ₆) = 0 ∧
    S.d2 (starRingEnd ℂ ∘ B.ξ₆) = 0 :=
  ⟨S.van2 B.irr_2 B.ξ₂_S2, S.van3 B.irr_2 B.ξ₂_S3, S.van1 B.irr_5 B.ξ₅_S1,
    S.van3 B.irr_5 B.ξ₅_S3, S.van1 B.irr_6 B.ξ₆_S1, S.van3 B.irr_6 B.ξ₆_S3,
    S.van1 (irr_conj B.irr_5) B.c5_S1, S.van2 (irr_conj B.irr_5) B.c5_S2,
    S.van1 (irr_conj B.irr_6) B.c6_S1, S.van2 (irr_conj B.irr_6) B.c6_S2⟩

omit [CharP K 3] in
theorem xi5_one_real : starRingEnd ℂ (B.ξ₅ 1) = B.ξ₅ 1 := by rw [← deg_eq B.irr_5]; simp
omit [CharP K 3] in
theorem xi6_one_real : starRingEnd ℂ (B.ξ₆ 1) = B.ξ₆ 1 := by rw [← deg_eq B.irr_6]; simp

omit [CharP K 3] in
theorem xi5_one : 2 * B.ξ₅ 1 = ((q : ℂ) - 1) * m * (q + 1 + 3 * m) := by
  rw [← deg_eq B.irr_5]
  have h' : ((2 * deg B.ξ₅ : ℤ) : ℂ) = ((((q : ℤ) - 1) * m * (q + 1 + 3 * m) : ℤ) : ℂ) := by
    rw [B.deg_5]
  push_cast at h'; exact h'

omit [CharP K 3] in
theorem xi6_one : 2 * B.ξ₆ 1 = ((q : ℂ) - 1) * m * (q + 1 - 3 * m) := by
  rw [← deg_eq B.irr_6]
  have h' : ((2 * deg B.ξ₆ : ℤ) : ℂ) = ((((q : ℤ) - 1) * m * (q + 1 - 3 * m) : ℤ) : ℂ) := by
    rw [B.deg_6]
  push_cast at h'; exact h'

include B hq hK hG hP1P hPc hPn hN1c in
theorem val_J_mul {x : G} (hη : ∀ i, D.η i x = 0) (hη' : ∀ i, D.η' i x = 0)
    (hO : ∀ O : S.Orbit, ∀ χ ∈ O.R, χ x = 0) {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    starRingEnd ℂ (χ S.J) * χ x =
      ((S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ)) * χ x := by
  by_cases hx0 : χ x = 0
  · rw [hx0, mul_zero, mul_zero]
  have hne : ∀ i, χ ≠ D.η i := fun i h => hx0 (by rw [h]; exact hη i)
  have hne' : ∀ i, χ ≠ D.η' i := fun i h => hx0 (by rw [h]; exact hη' i)
  have hR : ∀ θ ∈ S.W.RFam, S.dR χ θ = 0 := fun θ hθ => D.dR_other hχ hne hne' ⟨θ, hθ⟩
  have hS : ∀ θ ∈ S.W.SFam, S.dS χ θ = 0 := by
    intro θ hθ
    by_contra h
    obtain ⟨O, rfl⟩ := B.exists_orbit_of hq hK hG hP1P hPc hPn hN1c hθ
    exact hx0 (hO O χ (mem_supp.mpr ⟨hχ, h⟩))
  rw [val_J hχ, Finset.sum_eq_zero (fun θ hθ => by rw [hR θ hθ]; simp),
    Finset.sum_eq_zero (fun θ hθ => by rw [hS θ hθ]; simp)]
  ring

include B hq hK hG hP1P hPc hPn hN1c in
theorem sum_JJ {x : G} (hη : ∀ i, D.η i x = 0) (hη' : ∀ i, D.η' i x = 0)
    (hO : ∀ O : S.Orbit, ∀ χ ∈ O.R, χ x = 0) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J * χ S.J * starRingEnd ℂ (χ x) / χ 1 =
      ∑ χ ∈ (irreducibles_finite G).toFinset,
        ((S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ)) ^ 2 *
          starRingEnd ℂ (χ x) / χ 1 := by
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Set.Finite.mem_toFinset] at hχ
  have h := B.val_J_mul hq hK hG hP1P hPc hPn hN1c hη hη' hO hχ
  have h' := congrArg (starRingEnd ℂ) h
  simp only [map_mul, map_add, map_div₀, map_sub, map_intCast, map_natCast, map_one,
    map_ofNat, RCLike.conj_conj] at h'
  set c := (S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ) with hc
  calc χ S.J * χ S.J * starRingEnd ℂ (χ x) / χ 1
      = χ S.J * (χ S.J * starRingEnd ℂ (χ x)) / χ 1 := by ring
    _ = χ S.J * (c * starRingEnd ℂ (χ x)) / χ 1 := by rw [h']
    _ = c * (χ S.J * starRingEnd ℂ (χ x)) / χ 1 := by ring
    _ = c * (c * starRingEnd ℂ (χ x)) / χ 1 := by rw [h']
    _ = c ^ 2 * starRingEnd ℂ (χ x) / χ 1 := by ring

omit [CharP K 3] in
theorem sum_c_sq {x : G} (h2 : B.ξ₂ x = 0) (h3 : B.ξ₃ x = -1) (h4 : B.ξ₄ x = 0) {α β : ℂ}
    (h5 : B.ξ₅ x = α) (h6 : B.ξ₆ x = β) (hα : starRingEnd ℂ α = α)
    (hβ : starRingEnd ℂ β = β) (hq0 : (q : ℂ) ≠ 0) :
    ∑ χ ∈ (irreducibles_finite G).toFinset,
      ((S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ)) ^ 2 *
        starRingEnd ℂ (χ x) / χ 1 =
      1 - 1 / q + ((q : ℂ) - 1) ^ 2 * α / (2 * B.ξ₅ 1) +
        ((q : ℂ) - 1) ^ 2 * β / (2 * B.ξ₆ 1) := by
  set c : (G → ℂ) → ℂ := fun χ => (S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ)
    with hc
  have hsplit : ∀ χ : G → ℂ, c χ ^ 2 * starRingEnd ℂ (χ x) / χ 1 =
      (c χ * starRingEnd ℂ (χ x) / χ 1) * S.d1 χ + ((q : ℂ) - 1) / 2 *
        ((c χ * starRingEnd ℂ (χ x) / χ 1) * S.d2 χ +
          (c χ * starRingEnd ℂ (χ x) / χ 1) * S.d3 χ) := fun χ => by
    simp only [hc]; ring
  rw [Finset.sum_congr rfl fun χ _ => hsplit χ, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib,
    sum_irr_eq_sum_of_vanish (supp_sub S.d1) _ (fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ; rw [S.van1 hχ hnot]; simp),
    sum_irr_eq_sum_of_vanish (supp_sub S.d2) _ (fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ; rw [S.van2 hχ hnot]; simp),
    sum_irr_eq_sum_of_vanish (supp_sub S.d3) _ (fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ; rw [S.van3 hχ hnot]; simp)]
  rw [show supp S.d1 = S.S1 from rfl, show supp S.d2 = S.S2 from rfl,
    show supp S.d3 = S.S3 from rfl, B.sum_S1, B.sum_S2, B.sum_S3]
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := B.d_zero
  obtain ⟨hξ21, hξ31, hξ41⟩ := B.xi_one
  have hd50 : B.ξ₅ 1 ≠ 0 := by
    rw [← deg_eq B.irr_5]; exact_mod_cast (deg_pos B.irr_5).ne'
  have hd60 : B.ξ₆ 1 ≠ 0 := by
    rw [← deg_eq B.irr_6]; exact_mod_cast (deg_pos B.irr_6).ne'
  simp only [hc, Function.comp_apply, Pi.one_apply, S.one_row.1, S.one_row.2.1, S.one_row.2.2,
    B.d1_2, B.d1_3, B.d1_4, B.d2_3, B.d2_4, B.d2_5, B.d2_6, B.d3_3, B.d3_4, B.d3_c5, B.d3_c6,
    z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, h2, h3, h4, h5, h6, hα, hβ, map_zero, map_neg,
    map_one, B.xi5_one_real, B.xi6_one_real, hξ21, hξ31, hξ41]
  push_cast
  field_simp
  ring

omit [CharP K 3] in
theorem sum_xy {x y : G} (h2 : B.ξ₂ x = 0) (h3 : B.ξ₃ x = -1) (h4 : B.ξ₄ x = 0)
    (h2' : B.ξ₂ y = 0) (h3' : B.ξ₃ y = -1) (h4' : B.ξ₄ y = 0) {α β α' β' : ℂ}
    (h5 : B.ξ₅ x = α) (h6 : B.ξ₆ x = β) (h5' : B.ξ₅ y = α') (h6' : B.ξ₆ y = β')
    (hα : starRingEnd ℂ α = α) (hβ : starRingEnd ℂ β = β) (hα' : starRingEnd ℂ α' = α')
    (hβ' : starRingEnd ℂ β' = β') (hq0 : (q : ℂ) ≠ 0) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, (χ x * χ y / χ 1) *
        ((S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ)) =
      1 + 1 / (q : ℂ) ^ 2 - ((q : ℂ) - 1) * α * α' / B.ξ₅ 1 +
        ((q : ℂ) - 1) * β * β' / B.ξ₆ 1 := by
  have hsplit : ∀ χ : G → ℂ, (χ x * χ y / χ 1) *
      ((S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ)) =
      (χ x * χ y / χ 1) * S.d1 χ + ((q : ℂ) - 1) / 2 *
        ((χ x * χ y / χ 1) * S.d2 χ + (χ x * χ y / χ 1) * S.d3 χ) := fun χ => by ring
  rw [Finset.sum_congr rfl fun χ _ => hsplit χ, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib,
    sum_irr_eq_sum_of_vanish (supp_sub S.d1) _ (fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ; rw [S.van1 hχ hnot]; simp),
    sum_irr_eq_sum_of_vanish (supp_sub S.d2) _ (fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ; rw [S.van2 hχ hnot]; simp),
    sum_irr_eq_sum_of_vanish (supp_sub S.d3) _ (fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ; rw [S.van3 hχ hnot]; simp)]
  rw [show supp S.d1 = S.S1 from rfl, show supp S.d2 = S.S2 from rfl,
    show supp S.d3 = S.S3 from rfl, B.sum_S1, B.sum_S2, B.sum_S3]
  obtain ⟨hξ21, hξ31, hξ41⟩ := B.xi_one
  have hd50 : B.ξ₅ 1 ≠ 0 := by
    rw [← deg_eq B.irr_5]; exact_mod_cast (deg_pos B.irr_5).ne'
  have hd60 : B.ξ₆ 1 ≠ 0 := by
    rw [← deg_eq B.irr_6]; exact_mod_cast (deg_pos B.irr_6).ne'
  simp only [Function.comp_apply, Pi.one_apply, S.one_row.1, B.d1_2, B.d1_3, B.d1_4, B.d2_3,
    B.d2_4, B.d2_5, B.d2_6, B.d3_3, B.d3_4, B.d3_c5, B.d3_c6, h2, h3, h4, h5, h6, h2', h3', h4',
    h5', h6', hα, hβ, hα', hβ', B.xi5_one_real, B.xi6_one_real, hξ21, hξ31, hξ41]
  push_cast
  field_simp
  ring

omit [CharP K 3] in
theorem mul_self_of_cls_J {t : G} (ht : t ∈ cls S.J) : t * t = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (mem_cls.mp ht)
  have : t = c⁻¹ * S.J * c := by rw [← hc]; group
  rw [this]
  calc c⁻¹ * S.J * c * (c⁻¹ * S.J * c) = c⁻¹ * (S.J * S.J) * c := by group
    _ = 1 := by rw [S.J_mul]; group

omit [CharP K 3] in
theorem card_JJ_le (x : G) :
    ((cls S.J ×ˢ cls S.J).filter fun t => t.1 * t.2 = x).card ≤
      Nat.card (Subgroup.centralizer ({x} : Set G)) ∧
    (Nat.card (Subgroup.centralizer ({x} : Set G)) ≤
      ((cls S.J ×ˢ cls S.J).filter fun t => t.1 * t.2 = x).card →
      ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ d ∈ Subgroup.centralizer ({x} : Set G),
        c * d = d * c) := by
  set F := (cls S.J ×ˢ cls S.J).filter fun t => t.1 * t.2 = x with hF
  set C := Finset.univ.filter (· ∈ Subgroup.centralizer ({x} : Set G)) with hC
  have hCc : C.card = Nat.card (Subgroup.centralizer ({x} : Set G)) := card_filter_eq _
  rcases F.eq_empty_or_nonempty with h | ⟨t₀, ht₀⟩
  · rw [h, Finset.card_empty]
    refine ⟨Nat.zero_le _, fun h' => ?_⟩
    have := Nat.card_pos (α := Subgroup.centralizer ({x} : Set G))
    omega
  have hmem : ∀ t ∈ F, t.1 * t.1 = 1 ∧ t.2 * t.2 = 1 ∧ t.1 * t.2 = x := by
    intro t ht
    simp only [hF, Finset.mem_filter, Finset.mem_product] at ht
    exact ⟨mul_self_of_cls_J ht.1.1, mul_self_of_cls_J ht.1.2, ht.2⟩
  have hinv : ∀ t ∈ F, t.1 * x * t.1 = x⁻¹ := by
    intro t ht
    obtain ⟨e1, e2, h12⟩ := hmem t ht
    rw [← h12]
    calc t.1 * (t.1 * t.2) * t.1 = (t.1 * t.1) * t.2 * t.1 := by group
      _ = t.2 * t.1 := by rw [e1, one_mul]
      _ = (t.1 * t.2)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right e1, inv_eq_of_mul_eq_one_right e2]
  have hself : ∀ t ∈ F, t.1⁻¹ = t.1 := fun t ht => inv_eq_of_mul_eq_one_right (hmem t ht).1
  have hmap : Set.MapsTo (fun t : G × G => t₀.1⁻¹ * t.1) F C := by
    intro t ht
    simp only [hC, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : t₀.1⁻¹ * t.1 * x * (t₀.1⁻¹ * t.1)⁻¹ = x := by
      calc t₀.1⁻¹ * t.1 * x * (t₀.1⁻¹ * t.1)⁻¹ = t₀.1⁻¹ * (t.1 * x * t.1⁻¹) * t₀.1 := by group
        _ = t₀.1⁻¹ * (t.1 * x * t.1) * t₀.1 := by rw [hself t ht]
        _ = t₀.1⁻¹ * x⁻¹ * t₀.1 := by rw [hinv t ht]
        _ = (t₀.1⁻¹ * x * t₀.1)⁻¹ := by group
        _ = (t₀.1 * x * t₀.1)⁻¹ := by rw [hself t₀ ht₀]
        _ = x := by rw [hinv t₀ ht₀, inv_inv]
    calc t₀.1⁻¹ * t.1 * x = t₀.1⁻¹ * t.1 * x * (t₀.1⁻¹ * t.1)⁻¹ * (t₀.1⁻¹ * t.1) := by group
      _ = x * (t₀.1⁻¹ * t.1) := by rw [hconj]
  have hinj : Set.InjOn (fun t : G × G => t₀.1⁻¹ * t.1) F := by
    intro t ht t' ht' h
    simp only at h
    have h1 : t.1 = t'.1 := mul_left_cancel h
    have h2 : t.2 = t'.2 := by
      have e := (hmem t ht).2.2
      have e' := (hmem t' ht').2.2
      rw [h1] at e
      exact mul_left_cancel (e.trans e'.symm)
    exact Prod.ext h1 h2
  have hle := Finset.card_le_card_of_injOn _ hmap hinj
  refine ⟨hCc ▸ hle, fun hge => ?_⟩
  have himg : F.image (fun t : G × G => t₀.1⁻¹ * t.1) = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
      exact hmap ht
    · rw [Finset.card_image_of_injOn hinj, hCc]; exact hge
  have hsq : ∀ c ∈ Subgroup.centralizer ({x} : Set G), t₀.1 * c * (t₀.1 * c) = 1 := by
    intro c hc
    have hcC : c ∈ C := by simp [hC, hc]
    rw [← himg] at hcC
    obtain ⟨t, ht, htc⟩ := Finset.mem_image.mp hcC
    have : t.1 = t₀.1 * c := by rw [← htc]; group
    rw [← this]
    exact (hmem t ht).1
  have hJ0 := (hmem t₀ ht₀).1
  have hinvC : ∀ c ∈ Subgroup.centralizer ({x} : Set G), t₀.1 * c * t₀.1 = c⁻¹ := by
    intro c hc
    have h := hsq c hc
    calc t₀.1 * c * t₀.1 = t₀.1 * c * (t₀.1 * c) * c⁻¹ := by group
      _ = c⁻¹ := by rw [h, one_mul]
  intro c hc d hd
  have h1 := hinvC _ (Subgroup.mul_mem _ hc hd)
  have h2 : t₀.1 * (c * d) * t₀.1 = (t₀.1 * c * t₀.1) * (t₀.1 * d * t₀.1) := by
    calc t₀.1 * (c * d) * t₀.1 = t₀.1 * c * (t₀.1 * t₀.1) * d * t₀.1 := by rw [hJ0]; group
      _ = (t₀.1 * c * t₀.1) * (t₀.1 * d * t₀.1) := by group
  rw [h2, hinvC c hc, hinvC d hd] at h1
  have := congrArg (·⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at this
  exact this.symm

omit [CharP K 3] in
include S hq in
theorem odd_card_centralizer (hm : q = 3 * m ^ 2) {x : G} {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ q + 1 - 3 * m ∨ p ∣ q + 1 + 3 * m) (hpx : p ∣ orderOf x) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  have hpq : ¬ p ∣ q ∧ ¬ p ∣ q - 1 ∧ ¬ p ∣ q + 1 := by
    rcases hpN with h | h
    · obtain ⟨h1, h2, h3, -⟩ := prime_minus hq hm hp h; exact ⟨h1, h2, h3⟩
    · obtain ⟨h1, h2, h3, -⟩ := prime_plus hq hm hp h; exact ⟨h1, h2, h3⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({x} : Set G)) 2 hodd
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  obtain ⟨c, hc⟩ := isConj_iff.mp (S.involution_conj _ ht')
  have htx : (t : G) * x = x * t := (Subgroup.mem_centralizer_singleton_iff.mp t.2)
  have hy : c * x * c⁻¹ ∈ Subgroup.centralizer ({S.J} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * x * c⁻¹ * (c * t * c⁻¹) = c * (x * t) * c⁻¹ := by group
      _ = c * (t * x) * c⁻¹ := by rw [htx]
      _ = c * t * c⁻¹ * (c * x * c⁻¹) := by group
  have hord : orderOf (c * x * c⁻¹) = orderOf x := by
    rw [show c * x * c⁻¹ = MulAut.conj c x from rfl, MulEquiv.orderOf_eq]
  have hdvd : orderOf x ∣ Nat.card (Subgroup.centralizer ({S.J} : Set G)) := by
    rw [← hord, ← Subgroup.orderOf_mk (c * x * c⁻¹) hy]
    exact orderOf_dvd_natCard _
  have hCJ := S.card_C
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hCJ' : Nat.card (Subgroup.centralizer ({S.J} : Set G)) = q * ((q - 1) * (q + 1)) := by
    have h : ((Nat.card (Subgroup.centralizer ({S.J} : Set G)) : ℕ) : ℂ) =
        ((q * ((q - 1) * (q + 1)) : ℕ) : ℂ) := by
      rw [hCJ]; push_cast [hq1]; ring
    exact_mod_cast h
  rw [hCJ'] at hdvd
  have hp' := hpx.trans hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hp' with h | h
  · exact hpq.1 h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hpq.2.1 h
    · exact hpq.2.2 h

omit [CharP K 3] in
include hq in
theorem m_facts (hm : q = 3 * m ^ 2) :
    (m : ℂ) ≠ 0 ∧ (q : ℂ) = 3 * (m : ℂ) ^ 2 ∧ 3 * (m : ℂ) ^ 2 - 1 ≠ 0 ∧
      3 * (m : ℂ) ^ 2 + 1 ≠ 0 ∧ 3 * (m : ℂ) ^ 2 + 1 + 3 * m ≠ 0 ∧
      3 * (m : ℂ) ^ 2 + 1 - 3 * m ≠ 0 := by
  have hm1 : 1 ≤ m := by
    rw [m_eq hq hm]; exact Nat.one_le_pow _ _ (by norm_num)
  have hne : ∀ z : ℤ, z ≠ 0 → (z : ℂ) ≠ 0 := fun z hz => by exact_mod_cast hz
  refine ⟨by exact_mod_cast (show m ≠ 0 by omega), by rw [hm]; push_cast; ring, ?_, ?_, ?_, ?_⟩
  · have := hne (3 * (m : ℤ) ^ 2 - 1) (by nlinarith); push_cast at this; exact this
  · have := hne (3 * (m : ℤ) ^ 2 + 1) (by positivity); push_cast at this; exact this
  · have := hne (3 * (m : ℤ) ^ 2 + 1 + 3 * m) (by positivity); push_cast at this; exact this
  · have := hne (3 * (m : ℤ) ^ 2 + 1 - 3 * m) (by nlinarith); push_cast at this; exact this

include B hq hK hG hP1P hPc hPn hN1c in
theorem card_JJ_minus (hm : q = 3 * m ^ 2) {x : G} (hx : Odd (orderOf x)) {p : ℕ}
    (hp : p.Prime) (hpa : p ∣ q + 1 - 3 * m) (hpx : p ∣ orderOf x) :
    ((cls S.J ×ˢ cls S.J).filter fun t => t.1 * t.2 = x).card = q + 1 - 3 * m := by
  obtain ⟨h2, h4, h6, hη, hη', hO⟩ := B.van_minus hq hG hm hp hpa hpx
  obtain ⟨h3, h5⟩ := B.val_minus hq hG hm hx hp hpa hpx
  obtain ⟨hm0, hqm, h1, h2', hb, ha⟩ := m_facts hq hm
  have hq0 : (q : ℂ) ≠ 0 := by rw [hqm]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hm0)
  have hcm := class_mult S.J S.J x
  rw [B.sum_JJ hq hK hG hP1P hPc hPn hN1c hη hη' hO,
    B.sum_c_sq h2 h3 h4 h5 h6 (by simp) (by simp) hq0, S.card_C, hG] at hcm
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  push_cast [hq1] at hcm
  have hd60 : B.ξ₆ 1 ≠ 0 := by
    rw [← deg_eq B.irr_6]; exact_mod_cast (deg_pos B.irr_6).ne'
  have key := jj_alg_minus hqm hm0 h1 h2' hb B.xi5_one hd60 hcm
  have hle := hall_le hm
  have : (((q + 1 - 3 * m : ℕ) : ℂ)) = (q : ℂ) + 1 - 3 * m := by push_cast [hle]; ring
  exact_mod_cast key.trans this.symm

include B hq hK hG hP1P hPc hPn hN1c in
theorem card_JJ_plus (hm : q = 3 * m ^ 2) {x : G} (hx : Odd (orderOf x)) {p : ℕ}
    (hp : p.Prime) (hpb : p ∣ q + 1 + 3 * m) (hpx : p ∣ orderOf x) :
    ((cls S.J ×ˢ cls S.J).filter fun t => t.1 * t.2 = x).card = q + 1 + 3 * m := by
  obtain ⟨h2, h4, h5, hη, hη', hO⟩ := B.van_plus hq hG hm hp hpb hpx
  obtain ⟨h3, h6⟩ := B.val_plus hq hG hm hx hp hpb hpx
  obtain ⟨hm0, hqm, h1, h2', hb, ha⟩ := m_facts hq hm
  have hq0 : (q : ℂ) ≠ 0 := by rw [hqm]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hm0)
  have hcm := class_mult S.J S.J x
  rw [B.sum_JJ hq hK hG hP1P hPc hPn hN1c hη hη' hO,
    B.sum_c_sq h2 h3 h4 h5 h6 (by simp) (by simp) hq0, S.card_C, hG] at hcm
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  push_cast [hq1] at hcm
  have hd50 : B.ξ₅ 1 ≠ 0 := by
    rw [← deg_eq B.irr_5]; exact_mod_cast (deg_pos B.irr_5).ne'
  have key := jj_alg_plus hqm hm0 h1 h2' ha B.xi6_one hd50 hcm
  exact_mod_cast key

include B hq hK hG hP1P hPc hPn hN1c in
theorem card_JV (hm : q = 3 * m ^ 2) {x y : G} (hx : Odd (orderOf x)) (hy : Odd (orderOf y))
    (h2 : B.ξ₂ x = 0) (h3 : B.ξ₃ x = -1) (h4 : B.ξ₄ x = 0)
    (h2' : B.ξ₂ y⁻¹ = 0) (h3' : B.ξ₃ y⁻¹ = -1) (h4' : B.ξ₄ y⁻¹ = 0) {α β α' β' : ℂ}
    (h5 : B.ξ₅ x = α) (h6 : B.ξ₆ x = β) (h5' : B.ξ₅ y⁻¹ = α') (h6' : B.ξ₆ y⁻¹ = β')
    (hα : starRingEnd ℂ α = α) (hβ : starRingEnd ℂ β = β) (hα' : starRingEnd ℂ α' = α')
    (hβ' : starRingEnd ℂ β' = β') (hαα : α * α' = 0) (hββ : β * β' = 0) :
    ((cls S.J ×ˢ cls x).filter fun t => t.1 * t.2 = y).card *
      Nat.card (Subgroup.centralizer ({x} : Set G)) = (q ^ 2 + 1) * (q ^ 2 - q + 1) := by
  obtain ⟨hm0, hqm, h1, h2'', hb, ha⟩ := m_facts hq hm
  have hq0 : (q : ℂ) ≠ 0 := by rw [hqm]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hm0)
  have hcm := class_mult S.J x y
  have hyi : Odd (orderOf y⁻¹) := by rw [orderOf_inv]; exact hy
  have hsum : ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J * χ x * starRingEnd ℂ (χ y) / χ 1 =
      ∑ χ ∈ (irreducibles_finite G).toFinset, χ x * χ y⁻¹ * starRingEnd ℂ (χ S.J) / χ 1 := by
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [Set.Finite.mem_toFinset] at hχ
    have hreal : starRingEnd ℂ (χ S.J) = χ S.J := by rw [← inv_eq_conj hχ, S.J_inv]
    rw [hreal, inv_eq_conj hχ y]
    ring
  rw [hsum, B.sum_J hq hK hG hP1P hPc hPn hN1c hx hyi,
    B.sum_xy h2 h3 h4 h2' h3' h4' h5 h6 h5' h6' hα hβ hα' hβ' hq0, S.card_C, hG] at hcm
  rw [show ((q : ℂ) - 1) * α * α' = ((q : ℂ) - 1) * (α * α') by ring,
    show ((q : ℂ) - 1) * β * β' = ((q : ℂ) - 1) * (β * β') by ring, hαα, hββ] at hcm
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  push_cast [hq1] at hcm
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hc0 : (q : ℂ) * ((q : ℂ) ^ 2 - 1) ≠ 0 := by
    rw [hqm]
    have : (3 * (m : ℂ) ^ 2) ^ 2 - 1 = (3 * (m : ℂ) ^ 2 - 1) * (3 * (m : ℂ) ^ 2 + 1) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hm0)) (mul_ne_zero h1 h2'')
  set N := ((cls S.J ×ˢ cls x).filter fun t => t.1 * t.2 = y).card with hN
  set c := Nat.card (Subgroup.centralizer ({x} : Set G)) with hc
  have key : (N : ℂ) * (c : ℂ) = ((q : ℂ) ^ 2 + 1) * ((q : ℂ) ^ 2 - q + 1) := by
    apply mul_left_cancel₀ hc0
    rw [show (q : ℂ) * ((q : ℂ) ^ 2 - 1) * ((N : ℂ) * (c : ℂ)) =
        (N : ℂ) * ((q : ℂ) * ((q : ℂ) ^ 2 - 1)) * (c : ℂ) by ring, hcm]
    field_simp
    ring
  have : ((((q ^ 2 + 1) * (q ^ 2 - q + 1) : ℕ) : ℂ)) =
      ((q : ℂ) ^ 2 + 1) * ((q : ℂ) ^ 2 - q + 1) := by
    push_cast [hq2]; ring
  exact_mod_cast key.trans this.symm

omit [CharP K 3] in
include B hq hG in
theorem mul_card_dvd_minus (hm : q = 3 * m ^ 2) {x : G} (h5 : B.ξ₅ x = -1) :
    m * Nat.card (Subgroup.centralizer ({x} : Set G)) ∣
      2 * q ^ 3 * (q + 1) * (q + 1 - 3 * m) := by
  have hdvd := omega_dvd B.irr_5 x (t := -1) (by rw [h5]; simp)
  rw [mul_neg_one, dvd_neg] at hdvd
  have hcls := card_conjClass_mul_card_centralizer x
  set c := Nat.card (Subgroup.centralizer ({x} : Set G)) with hc
  set n := Nat.card (ConjClasses.mk x).carrier with hn
  have hle := hall_le hm
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hm1 : 1 ≤ m := by rw [m_eq hq hm]; exact Nat.one_le_pow _ _ (by norm_num)
  have h1 : ((q - 1) * m * (q + 1 + 3 * m) : ℕ) ∣ 2 * n := by
    have h2 : (((q - 1) * m * (q + 1 + 3 * m) : ℕ) : ℤ) = 2 * deg B.ξ₅ := by
      rw [B.deg_5]; push_cast [show 1 ≤ q by omega]; ring
    have : (((q - 1) * m * (q + 1 + 3 * m) : ℕ) : ℤ) ∣ ((2 * n : ℕ) : ℤ) := by
      rw [h2]; push_cast; exact mul_dvd_mul_left 2 hdvd
    exact_mod_cast this
  have h3 := mul_dvd_mul_right h1 c
  rw [mul_assoc 2 n c, hcls, card_G_hall hq hG hm] at h3
  have e1 : (q - 1) * m * (q + 1 + 3 * m) * c = ((q - 1) * (q + 1 + 3 * m)) * (m * c) := by ring
  have e2 : 2 * ((q + 1 - 3 * m) * (q ^ 3 * (q - 1) * (q + 1) * (q + 1 + 3 * m))) =
      ((q - 1) * (q + 1 + 3 * m)) * (2 * q ^ 3 * (q + 1) * (q + 1 - 3 * m)) := by ring
  rw [e1, e2] at h3
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos (by omega) (by omega)) h3

omit [CharP K 3] in
include B hq hG in
theorem mul_card_dvd_plus (hm : q = 3 * m ^ 2) {x : G} (h6 : B.ξ₆ x = 1) :
    m * Nat.card (Subgroup.centralizer ({x} : Set G)) ∣
      2 * q ^ 3 * (q + 1) * (q + 1 + 3 * m) := by
  have hdvd := omega_dvd B.irr_6 x (t := 1) (by rw [h6]; simp)
  rw [mul_one] at hdvd
  have hcls := card_conjClass_mul_card_centralizer x
  set c := Nat.card (Subgroup.centralizer ({x} : Set G)) with hc
  set n := Nat.card (ConjClasses.mk x).carrier with hn
  have hle := hall_le hm
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hm1 : 1 ≤ m := by rw [m_eq hq hm]; exact Nat.one_le_pow _ _ (by norm_num)
  have hlt : 3 * m < q + 1 := by rw [hm]; nlinarith
  have h1 : ((q - 1) * m * (q + 1 - 3 * m) : ℕ) ∣ 2 * n := by
    have h2 : (((q - 1) * m * (q + 1 - 3 * m) : ℕ) : ℤ) = 2 * deg B.ξ₆ := by
      rw [B.deg_6]; push_cast [show 1 ≤ q by omega, hle]; ring
    have : (((q - 1) * m * (q + 1 - 3 * m) : ℕ) : ℤ) ∣ ((2 * n : ℕ) : ℤ) := by
      rw [h2]; push_cast; exact mul_dvd_mul_left 2 hdvd
    exact_mod_cast this
  have h3 := mul_dvd_mul_right h1 c
  rw [mul_assoc 2 n c, hcls, card_G_hall hq hG hm] at h3
  have e1 : (q - 1) * m * (q + 1 - 3 * m) * c = ((q - 1) * (q + 1 - 3 * m)) * (m * c) := by ring
  have e2 : 2 * ((q + 1 - 3 * m) * (q ^ 3 * (q - 1) * (q + 1) * (q + 1 + 3 * m))) =
      ((q - 1) * (q + 1 - 3 * m)) * (2 * q ^ 3 * (q + 1) * (q + 1 + 3 * m)) := by ring
  rw [e1, e2] at h3
  have : 0 < q + 1 - 3 * m := by omega
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos (by omega) this) h3

omit [Group G] [Fintype G] [CharP K 3] in
include hq in
theorem dvd_of_hall_arith (hm : q = 3 * m ^ 2) {c n : ℕ}
    (h1 : c ∣ (q ^ 2 + 1) * (q ^ 2 - q + 1))
    (h2 : c ∣ q ^ 3 * ((q - 1) * (q + 1)) * (q ^ 2 - q + 1)) (hodd : Odd c)
    (h3 : m * c ∣ 2 * q ^ 3 * (q + 1) * n) : c ∣ n := by
  obtain ⟨c1, c2, c3, c4, -, c6⟩ := hall_coprime hm (m_odd hq hm)
  rw [mul_comm (q + 1 - 3 * m), ← hall_mul hm] at c1 c2 c3 c4
  set N := q ^ 2 - q + 1 with hN
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hcq : Nat.Coprime c q :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.mul_right c6.symm c1.symm).symm
  have h2' : c ∣ ((q - 1) * (q + 1)) * N := by
    rw [mul_assoc] at h2
    exact (Nat.Coprime.pow_right 3 hcq).dvd_of_dvd_mul_left h2
  have h4 : c ∣ 2 * N := by
    have := Nat.dvd_sub h1 h2'
    have e : (q ^ 2 + 1) * N - (q - 1) * (q + 1) * N = 2 * N := by
      rw [← Nat.sub_mul]
      congr 1
      have : (q - 1) * (q + 1) = q ^ 2 - 1 := by
        zify [hq1, Nat.one_le_pow 2 q (by omega)]; ring
      rw [this]; have : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
      omega
    rwa [e] at this
  have hc2 : Nat.Coprime c 2 := Nat.coprime_two_right.mpr hodd
  have hcN : c ∣ N := hc2.dvd_of_dvd_mul_left h4
  have hcop : Nat.Coprime c (2 * q ^ 3 * (q + 1)) :=
    Nat.Coprime.coprime_dvd_left hcN (Nat.Coprime.mul_right
      (Nat.Coprime.mul_right c4 (Nat.Coprime.pow_right 3 c1)) c3)
  exact hcop.dvd_of_dvd_mul_left ((Dvd.intro_left m rfl).trans h3)

omit [Group G] [Fintype G] [CharP K 3] in
include hq hG in
theorem card_G_N : Nat.card G = q ^ 3 * ((q - 1) * (q + 1)) * (q ^ 2 - q + 1) := by
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  rw [hG]
  zify [hq1, h2]
  ring

include B hq hK hG hP1P hPc hPn hN1c in
theorem centralizer_minus (hm : q = 3 * m ^ 2) {x : G} (hx : Odd (orderOf x)) {p : ℕ}
    (hp : p.Prime) (hpa : p ∣ q + 1 - 3 * m) (hpx : p ∣ orderOf x) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = q + 1 - 3 * m ∧
      ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ d ∈ Subgroup.centralizer ({x} : Set G),
        c * d = d * c := by
  have hJJ := B.card_JJ_minus hq hK hG hP1P hPc hPn hN1c hm hx hp hpa hpx
  obtain ⟨hle, hcomm⟩ := card_JJ_le (S := S) x
  rw [hJJ] at hle hcomm
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨p', hp', hp'b⟩ := Nat.exists_prime_and_dvd (show q + 1 + 3 * m ≠ 1 by omega)
  have : Fact p'.Prime := ⟨hp'⟩
  have hp'G : p' ∣ Nat.card G := by
    rw [card_G_hall hq hG hm]; exact Dvd.dvd.mul_left (dvd_mul_of_dvd_right hp'b _) _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p' hp'G
  have hp'2 := (prime_plus hq hm hp' hp'b).2.2.2.2
  have hyodd : Odd (orderOf y) := by rw [hy]; exact hp'.odd_of_ne_two hp'2
  have hyi : p' ∣ orderOf y⁻¹ := by rw [orderOf_inv, hy]
  have hyiodd : Odd (orderOf y⁻¹) := by rw [orderOf_inv]; exact hyodd
  obtain ⟨h2, h4, h6, -⟩ := B.van_minus hq hG hm hp hpa hpx
  obtain ⟨h3, h5⟩ := B.val_minus hq hG hm hx hp hpa hpx
  obtain ⟨h2', h4', h5', -⟩ := B.van_plus hq hG hm hp' hp'b hyi
  obtain ⟨h3', h6'⟩ := B.val_plus hq hG hm hyiodd hp' hp'b hyi
  have hJV := B.card_JV hq hK hG hP1P hPc hPn hN1c hm hx hyodd h2 h3 h4 h2' h3' h4' h5 h6 h5' h6'
    (by simp) (by simp) (by simp) (by simp) (by ring) (by ring)
  have hc1 : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ (q ^ 2 + 1) * (q ^ 2 - q + 1) :=
    Dvd.intro_left _ hJV
  have hc2 : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣
      q ^ 3 * ((q - 1) * (q + 1)) * (q ^ 2 - q + 1) := by
    rw [← card_G_N hq hG]; exact Subgroup.card_subgroup_dvd_card _
  have hodd := odd_card_centralizer (S := S) hq hm hp (Or.inl hpa) hpx
  have hdvd := dvd_of_hall_arith hq hm hc1 hc2 hodd (B.mul_card_dvd_minus hq hG hm h5)
  have hlt : 3 * m < q + 1 := by
    have hm1 : 1 ≤ m := by rw [m_eq hq hm]; exact Nat.one_le_pow _ _ (by norm_num)
    rw [hm]; nlinarith
  have hc := le_antisymm (Nat.le_of_dvd (by omega) hdvd) hle
  exact ⟨hc, hcomm hc.le⟩

include B hq hK hG hP1P hPc hPn hN1c in
theorem centralizer_plus (hm : q = 3 * m ^ 2) {x : G} (hx : Odd (orderOf x)) {p : ℕ}
    (hp : p.Prime) (hpb : p ∣ q + 1 + 3 * m) (hpx : p ∣ orderOf x) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = q + 1 + 3 * m ∧
      ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ d ∈ Subgroup.centralizer ({x} : Set G),
        c * d = d * c := by
  have hJJ := B.card_JJ_plus hq hK hG hP1P hPc hPn hN1c hm hx hp hpb hpx
  obtain ⟨hle, hcomm⟩ := card_JJ_le (S := S) x
  rw [hJJ] at hle hcomm
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hm1 : 1 ≤ m := by rw [m_eq hq hm]; exact Nat.one_le_pow _ _ (by norm_num)
  have hlt : 3 * m < q + 1 := by rw [hm]; nlinarith
  have ha1 : q + 1 - 3 * m ≠ 1 := by
    have hq27 : 27 ≤ q := S.q_ge
    have hm3 : 3 ≤ m := by nlinarith
    have : 3 * m + 3 ≤ q + 1 := by rw [hm]; nlinarith
    omega
  obtain ⟨p', hp', hp'a⟩ := Nat.exists_prime_and_dvd ha1
  have : Fact p'.Prime := ⟨hp'⟩
  have hp'G : p' ∣ Nat.card G := by
    rw [card_G_hall hq hG hm]; exact Dvd.dvd.mul_right hp'a _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p' hp'G
  have hp'2 := (prime_minus hq hm hp' hp'a).2.2.2.2
  have hyodd : Odd (orderOf y) := by rw [hy]; exact hp'.odd_of_ne_two hp'2
  have hyi : p' ∣ orderOf y⁻¹ := by rw [orderOf_inv, hy]
  have hyiodd : Odd (orderOf y⁻¹) := by rw [orderOf_inv]; exact hyodd
  obtain ⟨h2, h4, h5, -⟩ := B.van_plus hq hG hm hp hpb hpx
  obtain ⟨h3, h6⟩ := B.val_plus hq hG hm hx hp hpb hpx
  obtain ⟨h2', h4', h6', -⟩ := B.van_minus hq hG hm hp' hp'a hyi
  obtain ⟨h3', h5'⟩ := B.val_minus hq hG hm hyiodd hp' hp'a hyi
  have hJV := B.card_JV hq hK hG hP1P hPc hPn hN1c hm hx hyodd h2 h3 h4 h2' h3' h4' h5 h6 h5' h6'
    (by simp) (by simp) (by simp) (by simp) (by ring) (by ring)
  have hc1 : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ (q ^ 2 + 1) * (q ^ 2 - q + 1) :=
    Dvd.intro_left _ hJV
  have hc2 : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣
      q ^ 3 * ((q - 1) * (q + 1)) * (q ^ 2 - q + 1) := by
    rw [← card_G_N hq hG]; exact Subgroup.card_subgroup_dvd_card _
  have hodd := odd_card_centralizer (S := S) hq hm hp (Or.inr hpb) hpx
  have hdvd := dvd_of_hall_arith hq hm hc1 hc2 hodd (B.mul_card_dvd_plus hq hG hm h6)
  have hc := le_antisymm (Nat.le_of_dvd (by omega) hdvd) hle
  exact ⟨hc, hcomm hc.le⟩

end Block

end CFSG.Walter.WardLocal

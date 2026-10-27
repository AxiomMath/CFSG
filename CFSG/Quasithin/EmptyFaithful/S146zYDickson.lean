module

public import CFSG.Quasithin.Vol2.F134L2

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.F134
open scoped MatrixGroups

theorem dvd_two_pow_sub_one_of_psl2_two
    {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 ≤ n)
    (H : Subgroup PSL(2, GaloisField 2 n))
    (h2 : 2 ^ n ∣ Nat.card H) (hpH : p ∣ Nat.card H)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = p) : p ∣ 2 ^ n - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : ¬ 3 ∣ Nat.card H := fun h => by
    rcases hprime 3 Nat.prime_three h with h | h <;> omega
  have hp2 : ∀ k : ℕ, ¬ p ∣ 2 ^ k := fun k h => by
    have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  have h3dvd : ∀ k : ℕ, 3 ∣ 2 ^ (2 * k) - 1 := fun k => by
    have h : 2 ^ 2 - 1 ∣ 2 ^ (2 * k) - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_right 2 k)
    rwa [show (2 : ℕ) ^ 2 - 1 = 3 by norm_num] at h
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have h2' : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  have h4 : 4 ∣ Nat.card H := (pow_dvd_pow 2 hn).trans h2
  have hodd : ∀ z : ℕ, (z ∣ (2 ^ n + 1) / Nat.gcd 2 (2 ^ n - 1) ∨
      z ∣ (2 ^ n - 1) / Nat.gcd 2 (2 ^ n - 1)) → ¬ 2 ∣ z := by
    rintro z hz h2z
    rw [hgcd, Nat.div_one, Nat.div_one] at hz
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hev : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    rcases hz with hz | hz
    · have := h2z.trans hz
      omega
    · have := h2z.trans hz
      omega
  rcases F6.dicksonPSL2_holds 2 n (by omega) H with
      ⟨-, m, -, hm⟩ | ⟨-, hz⟩ | ⟨z, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, -, -, hPc, -, hQt, -, htq⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact absurd (hm ▸ hpH) (hp2 m)
  · exact absurd ((dvd_pow_self 2 (by omega : n ≠ 0)).trans h2) (hodd _ hz)
  · have hc := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at hc
    rw [hc] at h4
    exact (hodd z hz (by omega)).elim
  · exact absurd (by rw [Nat.card_congr e.toEquiv, card_alternating_four]; norm_num) h3
  · exact absurd (by rw [Nat.card_congr e.toEquiv, card_perm_four]; norm_num) h3
  · exact absurd (by rw [Nat.card_congr e.toEquiv, card_alternating_five]; norm_num) h3
  · have hHt : Nat.card H = t * 2 ^ m := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hQt, hPc]
    rw [hHt] at hpH
    have hpt : p ∣ t := ((Nat.Prime.dvd_mul hp).1 hpH).resolve_right (hp2 m)
    rw [hgcd, Nat.div_one] at htq
    exact hpt.trans htq
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hm
      omega
    have hc := Nat.card_congr e.toEquiv
    rw [card_psl2_two hm0] at hc
    exact absurd (by rw [hc]; exact Dvd.dvd.mul_left (h3dvd m) _) h3
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hm
      omega
    have hc := Nat.card_congr e.toEquiv
    have hK : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
    rw [CFSG.GorensteinWalter.pgl2_card_formula, hK, ← pow_mul, mul_comm m 2] at hc
    exact absurd (by rw [hc]; exact Dvd.dvd.mul_left (h3dvd m) _) h3

theorem psl2Borel_ge5 :
    ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m p : ℕ) (y : A),
      p.Prime → 5 ≤ p → IsPSL 2 2 m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      p ∣ 2 ^ m - 1 := by
  intro A _ _ L B U m p y hp hp5 hL hUB hBL hU hB hy hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hm1, -, h22, -⟩, -⟩ := id hL
  have hm : 2 ≤ m := by
    by_contra h
    have : m = 1 := by omega
    subst this
    exact h22 (by norm_num)
  have hcardL := CFSG.Quasithin.F420.card_of_statedPSL_two_two hL
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2 hL
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hU.2.1
  have hidx := (U.subgroupOf L).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv, hk, hcardL] at hidx
  have hcop : Nat.Coprime (2 ^ m) (U.subgroupOf L).index :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by
      have := hU.2.2
      omega)))
  have h2U : 2 ^ m ∣ Nat.card U := by
    rw [hk]
    exact hcop.dvd_of_dvd_mul_right (hidx ▸ Dvd.intro _ rfl)
  let H : Subgroup PSL(2, GaloisField 2 m) := (B.subgroupOf L).map e.toMonoidHom
  have hH : Nat.card H = Nat.card B := by
    rw [← Nat.card_congr ((B.subgroupOf L).equivMapOfInjective _ e.injective).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  refine dvd_two_pow_sub_one_of_psl2_two hp hp5 hm H ?_ ?_ ?_
  · rw [hH]
    exact h2U.trans (Subgroup.card_dvd_of_le hUB)
  · rw [hH, ← hyp]
    exact Subgroup.orderOf_dvd_natCard B hy
  · rw [hH]
    exact hB

end CFSG.Quasithin.S146zY

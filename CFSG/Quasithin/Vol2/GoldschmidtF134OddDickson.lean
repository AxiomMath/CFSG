module

public import CFSG.Quasithin.Background.F6CatDickson
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem nonempty_mulEquiv_psl2_odd {X : Type} [Group X] {p f : ℕ} [Fact p.Prime]
    (h : StatedClassicalModel X .PSL 2 p f) : Nonempty (X ≃* PSL(2, GaloisField p f)) := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (GaloisField p f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p f (by omega)]
  exact ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcardK)))⟩

theorem three_dvd_two_pow_two_mul_sub_one (m : ℕ) : 3 ∣ 2 ^ (2 * m) - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 4 1 m
  rw [one_pow] at h
  rw [pow_mul]
  exact h

theorem card_psl2_two_pow {m : ℕ} (hm : m ≠ 0) :
    Nat.card PSL(2, GaloisField 2 m) = 2 ^ m * (2 ^ (2 * m) - 1) := by
  have hK : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm
  rw [Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 m)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 2),
    show Finset.Icc 2 2 = {2} by decide, Finset.prod_singleton,
    show 2 * (2 - 1) / 2 = 1 from rfl, pow_one, hK]
  have hgcd : Nat.gcd 2 (2 ^ m - 1) = 1 := by
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 hm
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  rw [hgcd, Nat.div_one, ← pow_mul, mul_comm m 2]

theorem card_alternating_four' : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem card_alternating_five' : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem normal_of_card_two_pow {H : Type*} [Group H] [Finite H] {n t : ℕ} (hodd : Odd t)
    (hH : Nat.card H = t * 2 ^ n) {P S : Subgroup H} (hPn : P.Normal) (hP : Nat.card P = 2 ^ n)
    (hS : Nat.card S = 2 ^ n) : S.Normal := by
  have hP2 : IsPGroup 2 P := IsPGroup.of_card hP
  have hS2 : IsPGroup 2 S := IsPGroup.of_card hS
  have hsup : IsPGroup 2 ↥(S ⊔ P) := hS2.to_sup_of_normal_right' hP2 (by
    rw [Subgroup.normalizer_eq_top_iff.mpr hPn]
    exact le_top)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hsup
  have hdvd : Nat.card ↥(S ⊔ P) ∣ t * 2 ^ n := hH ▸ Subgroup.card_subgroup_dvd_card _
  have hcop : Nat.Coprime (2 ^ k) t := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hkn : 2 ^ k ∣ 2 ^ n := by
    rw [hk] at hdvd
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hle : k ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hkn
  have hSeq : S = S ⊔ P := Subgroup.eq_of_le_of_card_ge le_sup_left (by
    rw [hk, hS]
    exact Nat.pow_le_pow_right (by norm_num) hle)
  have hPS : P ≤ S := hSeq ▸ le_sup_right
  have hPS' : P = S := Subgroup.eq_of_le_of_card_ge hPS (by rw [hP, hS])
  rw [← hPS']
  exact hPn

theorem psl2_borel_core {n : ℕ} (hn : 2 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (H : Subgroup PSL(2, GaloisField 2 n))
    (h2 : 2 ^ n ∣ Nat.card H) (hpH : p ∣ Nat.card H)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = p) :
    p ∣ 2 ^ n - 1 ∧ ∀ S : Subgroup ↥H, Nat.card S = 2 ^ n → S.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hev : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  have h4 : 4 ∣ Nat.card H := (pow_dvd_pow 2 hn).trans h2
  have h3 : ¬ 3 ∣ Nat.card H := fun h => by
    rcases hprime 3 Nat.prime_three h with h | h <;> omega
  have hpnd : ∀ m : ℕ, ¬ p ∣ 2 ^ m := fun m h => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega
  have hodd : ∀ z : ℕ, (z ∣ (2 ^ n + 1) / Nat.gcd 2 (2 ^ n - 1) ∨
      z ∣ (2 ^ n - 1) / Nat.gcd 2 (2 ^ n - 1)) → ¬ 2 ∣ z := by
    rintro z hz h2z
    rw [hgcd, Nat.div_one, Nat.div_one] at hz
    rcases hz with hz | hz
    · have := h2z.trans hz
      omega
    · have := h2z.trans hz
      omega
  rcases F6.dicksonPSL2_holds 2 n (by omega) H with
      ⟨-, m, -, hm⟩ | ⟨-, hz⟩ | ⟨z, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, hPn, -, hPc, -, hQt, -, htq⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact absurd (hm ▸ hpH) (hpnd m)
  · exact absurd (hev.trans h2) (hodd _ hz)
  · have hc := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at hc
    rw [hc] at h4
    exact (hodd z hz (by omega)).elim
  · exact absurd (by rw [Nat.card_congr e.toEquiv, card_alternating_four']; norm_num) h3
  · exfalso
    have h1' : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have h2' : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
    have : 2 ∣ 2 ^ (2 * n) - 1 := (by norm_num : 2 ∣ 16).trans h16
    omega
  · exact absurd (by rw [Nat.card_congr e.toEquiv, card_alternating_five']; norm_num) h3
  · have hHt : Nat.card H = t * 2 ^ m := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hQt, hPc]
    have hpt : p ∣ t := ((Nat.Prime.dvd_mul hp).1 (hHt ▸ hpH)).resolve_right (hpnd m)
    rw [hgcd, Nat.div_one] at htq
    have hodd1 : Odd (2 ^ n - 1) := Nat.odd_iff.mpr (by omega)
    have htodd : Odd t := hodd1.of_dvd_nat htq
    have hodd2 : Odd (2 ^ (2 * n) - 1) := Nat.odd_iff.mpr (by
      have h1' : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
      have h2' : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
      omega)
    have hmn : m = n := by
      have hdvdL : t * 2 ^ m ∣ 2 ^ n * (2 ^ (2 * n) - 1) := by
        rw [← hHt, ← card_psl2_two_pow (by omega : n ≠ 0)]
        exact Subgroup.card_subgroup_dvd_card H
      have hm1 : 2 ^ m ∣ 2 ^ n * (2 ^ (2 * n) - 1) := (Dvd.intro_left t rfl).trans hdvdL
      have hcop : Nat.Coprime (2 ^ m) (2 ^ (2 * n) - 1) :=
        Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd2)
      have hle : m ≤ n :=
        (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right hm1)
      have hcop2 : Nat.Coprime (2 ^ n) t :=
        Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr htodd)
      have h2m : 2 ^ n ∣ 2 ^ m := by
        have : 2 ^ n ∣ t * 2 ^ m := hHt ▸ h2
        exact hcop2.dvd_of_dvd_mul_left this
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2m
      omega
    subst hmn
    exact ⟨hpt.trans htq, fun S hS => normal_of_card_two_pow htodd hHt hPn hPc hS⟩
  · exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hm
      omega
    apply h3
    rw [Nat.card_congr e.toEquiv, card_psl2_two_pow hm0]
    exact (three_dvd_two_pow_two_mul_sub_one m).mul_left _
  · exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hm
      omega
    have hc := Nat.card_congr e.toEquiv
    have hK : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
    rw [CFSG.GorensteinWalter.pgl2_card_formula, hK, ← pow_mul, mul_comm m 2] at hc
    apply h3
    rw [hc]
    exact (three_dvd_two_pow_two_mul_sub_one m).mul_left _

end CFSG.Quasithin.H13.NQCore

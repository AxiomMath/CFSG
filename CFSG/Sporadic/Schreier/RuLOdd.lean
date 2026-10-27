module

public import CFSG.Sporadic.Schreier.RuLGroup

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

theorem mem_of_orderOf_prime_of_normal {L : Type*} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : ¬ p ^ 2 ∣ Nat.card L) (R : Subgroup L) [R.Normal] (hR : p ∣ Nat.card R) {y : L}
    (hy : orderOf y = p) : y ∈ R := by
  have hcard : Nat.card L = Nat.card R * Nat.card (L ⧸ R) := by
    rw [mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup R
  have hq : ¬ p ∣ Nat.card (L ⧸ R) := fun h => hp2 (by
    rw [hcard, pow_two]
    exact Nat.mul_dvd_mul hR h)
  have h1 : orderOf (QuotientGroup.mk y : L ⧸ R) ∣ p :=
    hy ▸ orderOf_map_dvd (QuotientGroup.mk' R) y
  have h2 : orderOf (QuotientGroup.mk y : L ⧸ R) ∣ Nat.card (L ⧸ R) := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
  · exact absurd (h ▸ h2) hq

theorem two_dvd_orderOf {G : Type*} [Group G] {v : G} {k : ℕ} (h1 : v ≠ 1)
    (h2 : v ^ (2 ^ k) = 1) : 2 ∣ orderOf v := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2)
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact absurd hj h1
  · rw [hj, pow_succ]
    exact Dvd.intro_left _ rfl

theorem prime_dvd_card_ruL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 116480) :
    p ∈ [5, 7, 13] := by
  have e : (116480 : ℕ) = 2 ^ 8 * (5 * (7 * 13)) := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · simp [(Nat.prime_dvd_prime_iff_eq hp (by decide)).1 h]
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · simp [(Nat.prime_dvd_prime_iff_eq hp (by decide)).1 h]
  · simp [(Nat.prime_dvd_prime_iff_eq hp (by decide)).1 h]

theorem ruL_noOddNormal
    (R : Subgroup ruL) (hR : R.Normal) (hodd : Odd (Nat.card R)) :
    R = ⊥ := by
  by_contra hne
  have hfin : Finite ruL := Nat.finite_of_card_ne_zero (by rw [card_ruL]; norm_num)
  have h1 : Nat.card R ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  obtain ⟨p, hp, hpR⟩ := Nat.exists_prime_and_dvd h1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpR)
  have hpL : p ∣ 116480 := card_ruL ▸ hpR.trans (Subgroup.card_subgroup_dvd_card R)
  have hmem := prime_dvd_card_ruL hp hp2 hpL
  have hsq : ¬ p ^ 2 ∣ Nat.card ruL := by
    rw [card_ruL]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> decide
  let y : ruL := ⟨ruYp p, ruYp_memL p⟩
  have hy : orderOf y = p := by
    rw [← orderOf_ruYp hmem, ← Subgroup.orderOf_coe]
  have hyR : y ∈ R := mem_of_orderOf_prime_of_normal hp hsq R hpR hy
  let l : ruL := ⟨ruLGen 3, ruLGen_memL 3⟩
  have hvR : (y * (l * y * l⁻¹)) ^ 455 ∈ R :=
    R.pow_mem (R.mul_mem hyR (hR.conj_mem y hyR l)) 455
  have hv1 : (y * (l * y * l⁻¹)) ^ 455 ≠ 1 := fun h =>
    ruVp_ne_one hmem (by simpa [y, l] using congrArg Subtype.val h)
  have hv2 : ((y * (l * y * l⁻¹)) ^ 455) ^ (2 ^ 8) = 1 :=
    Subtype.ext (by simpa [y, l] using ruVp_pow hmem)
  have h2 : 2 ∣ orderOf (⟨_, hvR⟩ : R) := by
    rw [Subgroup.orderOf_mk]
    exact two_dvd_orderOf hv1 hv2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans (orderOf_dvd_natCard _)))

theorem CTUC_Ru_explicit_commuting_subgroup_odd_normal_exclusion :
    ruL ≤ ruP ⊓ Subgroup.centralizer {ruA0} ∧ Nat.card ruL = 116480 ∧
    (116480 : ℕ) = 2 ^ 8 * 5 * 7 * 13 ∧
    (∀ p ∈ [5, 7, 13], orderOf (ruYp p) = p ∧
      (ruYp p * (ruLGen 3 * ruYp p * (ruLGen 3)⁻¹)) ^ 455 ≠ 1 ∧
      ((ruYp p * (ruLGen 3 * ruYp p * (ruLGen 3)⁻¹)) ^ 455) ^ 256 = 1) ∧
    ∀ R : Subgroup ruL, R.Normal → Odd (Nat.card R) → R = ⊥ :=
  ⟨ruL_le_centralizer, card_ruL, by norm_num,
    fun _ hp => ⟨orderOf_ruYp hp, ruVp_ne_one hp, ruVp_pow hp⟩, ruL_noOddNormal⟩

end CFSG.Sporadic.RuSchreier

module

public import CFSG.RankThree.Coprime.ThetaPlaneNormalizesComponent
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

theorem exists_three_lift {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hker : ∀ a, f a = 1 → ∃ k : ℕ, a ^ 2 ^ k = 1) {b : B} (hb : b ∈ f.range)
    (h3 : b ^ 3 = 1) : ∃ a : A, a ^ 3 = 1 ∧ f a = b := by
  obtain ⟨a₀, rfl⟩ := hb
  obtain ⟨k, hk⟩ := hker (a₀ ^ 3) (by rw [map_pow, h3])
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) (by norm_num : 1 < 3)
  refine ⟨a₀ ^ (2 ^ k * m), ?_, ?_⟩
  · rw [← pow_mul, show 2 ^ k * m * 3 = 3 * 2 ^ k * m by ring, pow_mul, pow_mul, hk, one_pow]
  · rw [map_pow, pow_eq_pow_mod _ h3, hm, pow_one]

section E27

open scoped Pointwise

variable {G : Type*} [Group G]

theorem commute_of_card_three [Finite G] {Q : Subgroup G} (hQ : Nat.card Q = 3) {p : G}
    (hp : p ^ 3 = 1) (hpN : p ∈ Subgroup.normalizer (Q : Set G)) {q : G} (hq : q ∈ Q) :
    p * q = q * p := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hq1 : q = 1
  · rw [hq1, mul_one, one_mul]
  have hq3 : q ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Q) (x := ⟨q, hq⟩)
    rw [hQ] at this
    exact congrArg Subtype.val this
  have hoq : orderOf q = 3 := orderOf_eq_prime hq3 hq1
  have hzQ : Subgroup.zpowers q = Q := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hq) ?_
    rw [hQ, Nat.card_zpowers, hoq]
  have hc : p * q * p⁻¹ ∈ Subgroup.zpowers q := by
    rw [hzQ]
    exact (Subgroup.mem_normalizer_iff.mp hpN q).mp hq
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hoq, Finset.mem_image] at hc
  obtain ⟨m, hm, hpq⟩ := hc
  rw [Finset.mem_range] at hm
  interval_cases m
  · exfalso
    apply hq1
    have h : q = p⁻¹ * (p * q * p⁻¹) * p := by group
    rw [← hpq, pow_zero] at h
    simpa using h
  · rw [pow_one] at hpq
    calc p * q = p * q * p⁻¹ * p := by group
      _ = q * p := by rw [← hpq]
  · exfalso
    have e2 : p * p * q * (p * p)⁻¹ = q := by
      calc p * p * q * (p * p)⁻¹ = p * (p * q * p⁻¹) * p⁻¹ := by group
        _ = p * q ^ 2 * p⁻¹ := by rw [← hpq]
        _ = (p * q * p⁻¹) ^ 2 := by rw [conj_pow]
        _ = (q ^ 2) ^ 2 := by rw [← hpq]
        _ = q ^ 3 * q := by rw [← pow_mul, ← pow_succ]
        _ = q := by rw [hq3, one_mul]
    have e3 : p * p * p * q * (p * p * p)⁻¹ = q ^ 2 := by
      calc p * p * p * q * (p * p * p)⁻¹ = p * (p * p * q * (p * p)⁻¹) * p⁻¹ := by group
        _ = p * q * p⁻¹ := by rw [e2]
        _ = q ^ 2 := hpq.symm
    rw [← pow_three', hp, one_mul, inv_one, mul_one, sq] at e3
    apply hq1
    have := congrArg (fun z => q⁻¹ * z) e3
    simp only [inv_mul_cancel, inv_mul_cancel_left] at this
    exact this.symm

theorem three_le_pRank [Finite G] {P R H : Subgroup G} (hPH : P ≤ H) (hRH : R ≤ H)
    (hPN : P ≤ Subgroup.normalizer (R : Set G)) (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hP3 : ∀ a ∈ P, a ^ 3 = 1) (hP9 : 9 ≤ Nat.card P) (hPR : P ⊓ R = ⊥)
    (h3 : 3 ∣ Nat.card R) (h9 : ¬ 9 ∣ Nat.card R) : 3 ≤ CFSG.Open.pRank 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := fun g => ⟨1, Subtype.ext (by simpa using hP3 g g.2)⟩
  obtain ⟨Q, hQR, hQp, hQdvd, hPQ, -⟩ :=
    CFSG.RankThree.Coprime.exists_sylow_normalized R P hPp hPN
  have hQ3 : Nat.card Q = 3 := by
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    have h1 : 3 ∣ Nat.card Q := hQdvd 1 (by simpa using h3)
    have h2 : Nat.card Q ∣ Nat.card R := Subgroup.card_dvd_of_le hQR
    rw [hn] at h1 h2 ⊢
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0] at h1; norm_num at h1
      · exact h0
    have hn2 : n ≤ 1 := by
      by_contra h
      exact h9 ((show 9 = 3 ^ 2 by norm_num) ▸ (pow_dvd_pow 3 (by omega)).trans h2)
    rw [show n = 1 by omega, pow_one]
  obtain ⟨⟨x, hxQ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Q)).mp (by
    intro h
    rw [h, Subgroup.card_bot] at hQ3
    norm_num at hQ3)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hcomm : ∀ a ∈ P, ∀ q ∈ Q, a * q = q * a := fun a ha q hq =>
    commute_of_card_three hQ3 (hP3 a ha) (hPQ ha) hq
  have hQc : Q ≤ Subgroup.centralizer (P : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha q hq
  have hQ3' : ∀ q ∈ Q, q ^ 3 = 1 := fun q hq => by
    have := pow_card_eq_one' (G := ↥Q) (x := ⟨q, hq⟩)
    rw [hQ3] at this
    exact congrArg Subtype.val this
  have hQab : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q := by
    have hcyc : IsCyclic ↥Q := isCyclic_of_prime_card hQ3
    intro q hq q' hq'
    have := hcyc.commGroup.mul_comm ⟨q, hq⟩ ⟨q', hq'⟩
    exact congrArg Subtype.val this
  set E := P ⊔ Q with hE
  have hEset : (E : Set G) = (P : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P Q
      (hQc.trans (Subgroup.centralizer_le_normalizer _))
  have hmemE : ∀ e ∈ E, ∃ a ∈ P, ∃ q ∈ Q, e = a * q := fun e he => by
    have he' : e ∈ (E : Set G) := he
    rw [hEset] at he'
    obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp he'
    exact ⟨a, ha, q, hq, rfl⟩
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := fun e he => by
    obtain ⟨a, ha, q, hq, rfl⟩ := hmemE e he
    rw [(Commute.mul_pow (hcomm a ha q hq) 3), hP3 a ha, hQ3' q hq, one_mul]
  have hEc : E ≤ Subgroup.centralizer (E : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun f hf => by
      obtain ⟨a, ha, q, hq, rfl⟩ := hmemE e he
      obtain ⟨b, hb, r, hr, rfl⟩ := hmemE f hf
      calc b * r * (a * q) = (b * a) * (r * q) := by
              rw [mul_assoc, ← mul_assoc r, ← hcomm a ha r hr]; group
        _ = (a * b) * (q * r) := by rw [hPc b hb a ha, hQab r hr q hq]
        _ = a * q * (b * r) := by
              rw [mul_assoc, ← mul_assoc b, hcomm b hb q hq]; group
  have hEel : CFSG.Open.IsElemAbelian 3 E :=
    ⟨Subgroup.le_centralizer_iff_isMulCommutative.mp hEc, hE3⟩
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE3 g g.2)⟩
  obtain ⟨j, hj⟩ := hEp.exists_card_eq
  have hlt : P < E := by
    refine lt_of_le_of_ne le_sup_left fun h => hx1' ?_
    have hxP : x ∈ P := h ▸ Subgroup.mem_sup_right hxQ
    have : x ∈ P ⊓ R := ⟨hxP, hQR hxQ⟩
    rwa [hPR, Subgroup.mem_bot] at this
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [hj] at hcard
  replace hcard : 9 < 3 ^ j := lt_of_le_of_lt hP9 hcard
  have hj3 : 3 ≤ j := by
    by_contra h
    have : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hj3.trans (CFSG.SectionRank.le_pRank (by norm_num)
    (sup_le hPH (hQR.trans hRH)) hEel hj)

end E27

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS

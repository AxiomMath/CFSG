module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Ord
public import CFSG.RankThree.SubgroupLists.LinearTwoFamily

public section

namespace CFSG.Quasithin.A312U3

open CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

theorem coprime_self_pow_add_one {p k : ℕ} (hk : 1 ≤ k) : Nat.Coprime p (p ^ k + 1) := by
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hℓp hℓq
  have h1 : ℓ ∣ p ^ k := hℓp.trans (dvd_pow_self p (by omega))
  have h2 : ℓ ∣ p ^ k + 1 - p ^ k := Nat.dvd_sub hℓq h1
  rw [show p ^ k + 1 - p ^ k = 1 by omega] at h2
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)

theorem eq_one_of_card_psl2_dvd_su3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) : f = 1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp2' : 9 ≤ p ^ 2 := by nlinarith
  have hp3' : 27 ≤ p ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
  have hf3 : f ≤ 3 := by
    have hq2 : 2 ∣ (p ^ f) ^ 2 - 1 := by
      obtain ⟨k, hk⟩ := (hodd.pow (n := f)).pow (n := 2)
      exact ⟨k, by omega⟩
    have hqd : p ^ f ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
      refine dvd_trans ?_ h
      rw [Nat.mul_div_assoc _ hq2]
      exact Dvd.intro _ rfl
    have hcop : Nat.Coprime (p ^ f) ((p ^ 2 - 1) * (p ^ 3 + 1)) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.mul_right
        (coprime_self_pow_sub_one (by omega) (by norm_num))
        (coprime_self_pow_add_one (by norm_num)))
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hcop.dvd_of_dvd_mul_right hqd)
  interval_cases f
  · rfl
  ·
    exfalso
    obtain ⟨m, hm⟩ : ∃ m, p ^ 2 + 1 = 2 * m := by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨2 * k ^ 2 + 2 * k + 1, by rw [hk]; ring⟩
    have hsq : (p ^ 2) ^ 2 - 1 = (p ^ 2 - 1) * (2 * m) := by
      rw [← hm, mul_comm, ← Nat.sq_sub_sq, one_pow]
    have hN : p ^ 2 * ((p ^ 2) ^ 2 - 1) / 2 = p ^ 2 * (p ^ 2 - 1) * m := by
      rw [hsq, show p ^ 2 * ((p ^ 2 - 1) * (2 * m)) = 2 * (p ^ 2 * (p ^ 2 - 1) * m) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hN, show p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) =
      p ^ 2 * (p ^ 2 - 1) * (p * (p ^ 3 + 1)) by ring] at h
    have hpos : 0 < p ^ 2 * (p ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
    have h1 : m ∣ p * (p ^ 3 + 1) := Nat.dvd_of_mul_dvd_mul_left hpos h
    have hcop : Nat.Coprime m p := by
      apply Nat.coprime_of_dvd
      intro ℓ hℓ hℓm hℓp
      have h2 : ℓ ∣ p ^ 2 + 1 := hm ▸ hℓm.mul_left 2
      have h3 : ℓ ∣ p ^ 2 := hℓp.trans (dvd_pow_self p (by norm_num))
      have h4 : ℓ ∣ p ^ 2 + 1 - p ^ 2 := Nat.dvd_sub h2 h3
      rw [show p ^ 2 + 1 - p ^ 2 = 1 by omega] at h4
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h4)
    have h2 : m ∣ p ^ 3 + 1 := hcop.dvd_of_dvd_mul_left h1
    have h3 : m ∣ p ^ 3 + p := ⟨2 * p, by nlinarith [hm]⟩
    have h4 : m ∣ (p ^ 3 + p) - (p ^ 3 + 1) := Nat.dvd_sub h3 h2
    rw [show (p ^ 3 + p) - (p ^ 3 + 1) = p - 1 by omega] at h4
    have h5 := Nat.le_of_dvd (by omega) h4
    have h5' : m + 1 ≤ p := by omega
    nlinarith [hm, h5']
  ·
    exfalso
    obtain ⟨k, hk⟩ : ∃ k, p ^ 3 + 1 = 2 * k := by
      obtain ⟨t, ht⟩ := hodd.pow (n := 3)
      exact ⟨t + 1, by omega⟩
    have hsq : (p ^ 3) ^ 2 - 1 = (p ^ 3 - 1) * (2 * k) := by
      rw [← hk, mul_comm, ← Nat.sq_sub_sq, one_pow]
    have hN : p ^ 3 * ((p ^ 3) ^ 2 - 1) / 2 = p ^ 3 * (p ^ 3 - 1) * k := by
      rw [hsq, show p ^ 3 * ((p ^ 3 - 1) * (2 * k)) = 2 * (p ^ 3 * (p ^ 3 - 1) * k) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hN, hk, show p ^ 3 * ((p ^ 2 - 1) * (2 * k)) =
      p ^ 3 * k * (2 * (p ^ 2 - 1)) by ring,
      show p ^ 3 * (p ^ 3 - 1) * k = p ^ 3 * k * (p ^ 3 - 1) by ring] at h
    have hpos : 0 < p ^ 3 * k := Nat.mul_pos (by positivity) (by omega)
    have h1 : p ^ 3 - 1 ∣ 2 * (p ^ 2 - 1) := Nat.dvd_of_mul_dvd_mul_left hpos h
    have h2 := Nat.le_of_dvd (by omega) h1
    have h3 : 3 * p ^ 2 ≤ p ^ 3 :=
      calc 3 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hp3
        _ = p ^ 3 := by ring
    omega

theorem su3_psl2_defining_f {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) {M : Subgroup ↥(StatedSU 3 (p ^ 1) K)}
    {H : Subgroup (GL (Fin 3) K)} (h : QCtx p K M H) {f : ℕ} (hf : 1 ≤ f) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ f)
    (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) : f = 1 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hS : Nat.card (H ⧸ Subgroup.center H) = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL_two hodd.pow hF]
  have h5 : Nat.card (H ⧸ Subgroup.center H) ∣ Nat.card H := Subgroup.card_quotient_dvd_card _
  exact eq_one_of_card_psl2_dvd_su3 hp hp2 hf (hS ▸ h5.trans (card_dvd_of_qctx hK h))

end CFSG.Quasithin.A312U3

module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Quasi

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory
open CFSG.SectionRank.OddCover
open scoped MatrixGroups

variable {p : ℕ} {K : Type} [Field K] [Finite K]

theorem card_su3_eq [Fact p.Prime] (hK : Nat.card K = p ^ 2) :
    Nat.card ↥(StatedSU 3 (p ^ 1) K) = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  have := charP_of_card_sq (p := p) hK
  have h := card_statedSU_three (K := K) (p := p) (f := 1) (by rw [pow_one]; exact hK)
  rw [h]
  simp only [pow_one]
  ring

theorem card_dvd_of_qctx [Fact p.Prime] (hK : Nat.card K = p ^ 2)
    {M : Subgroup ↥(StatedSU 3 (p ^ 1) K)} {H : Subgroup (GL (Fin 3) K)} (h : QCtx p K M H) :
    Nat.card H ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  have h1 : Nat.card H ∣ Nat.card (M.map (StatedSU 3 (p ^ 1) K).subtype) :=
    Subgroup.card_dvd_of_le h.le
  rw [Subgroup.card_map_of_injective (StatedSU 3 (p ^ 1) K).subtype_injective] at h1
  exact h1.trans ((Subgroup.card_subgroup_dvd_card M).trans (card_su3_eq hK).dvd)

omit [Finite K] in
theorem card_eq_quotient_mul (H : Subgroup (GL (Fin 3) K)) :
    Nat.card H = Nat.card (H ⧸ Subgroup.center H) * Nat.card (Subgroup.center H) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem card_psl3_mul_gcd :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 3) K) * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  have h := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := 3)
    (by norm_num)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at h
  have hc := (Subgroup.center SL(3, K)).card_eq_card_quotient_mul_card_subgroup
  rw [h, Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity'
    (⟨0, by norm_num⟩ : Fin 3)).toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd,
    Fintype.card_fin, Nat.gcd_comm] at hc
  norm_num at hc
  exact hc.symm

theorem false_of_psl3_card_p (hp3 : 3 ≤ p) {s c d : ℕ} (hd : d ∣ 3)
    (hs : s * d = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)))
    (hdvd : s * c ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) : False := by
  obtain ⟨u, hu⟩ := hdvd
  have hp3' : 27 ≤ p ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
  have hp2' : 9 ≤ p ^ 2 := by nlinarith
  have hd1 : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
  have hpos : 0 < p ^ 3 * (p ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
  have key : (p ^ 3 + 1) * d = (p ^ 3 - 1) * (c * u) := by
    have h1 : p ^ 3 * (p ^ 2 - 1) * ((p ^ 3 + 1) * d) =
        p ^ 3 * (p ^ 2 - 1) * ((p ^ 3 - 1) * (c * u)) := by
      calc p ^ 3 * (p ^ 2 - 1) * ((p ^ 3 + 1) * d)
          = (p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) * d := by ring
        _ = (s * c * u) * d := by rw [hu]
        _ = (s * d) * (c * u) := by ring
        _ = p ^ 3 * (p ^ 2 - 1) * ((p ^ 3 - 1) * (c * u)) := by rw [hs]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hdvd2 : (p ^ 3 - 1) ∣ 2 * d := by
    have h2 : (p ^ 3 - 1) ∣ (p ^ 3 + 1) * d := ⟨c * u, key⟩
    have h3 : (p ^ 3 - 1) ∣ (p ^ 3 - 1) * d := dvd_mul_right _ _
    have h4 : (p ^ 3 + 1) * d = (p ^ 3 - 1) * d + 2 * d := by
      have : p ^ 3 + 1 = (p ^ 3 - 1) + 2 := by omega
      rw [this]; ring
    rw [h4] at h2
    exact (Nat.dvd_add_right h3).mp h2
  have hle := Nat.le_of_dvd (by positivity) hdvd2
  have hd3 : d ≤ 3 := Nat.le_of_dvd (by norm_num) hd
  omega

theorem false_of_card_p_six [Fact p.Prime] (hp3 : 3 < p) {s c d : ℕ} (hd : d ∣ 3) (hc : c ∣ 3)
    (hs : s * d = (p ^ 2) ^ 3 * (((p ^ 2) ^ 2 - 1) * ((p ^ 2) ^ 3 - 1)))
    (hdvd : s * c ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) : False := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  have hpd : Nat.Coprime (p ^ 6) d :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right hd hcop)
  have hpc : Nat.Coprime (p ^ 6) c :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right hc hcop)
  have h6s : p ^ 6 ∣ s * d := by
    rw [hs]
    exact ⟨((p ^ 2) ^ 2 - 1) * ((p ^ 2) ^ 3 - 1), by ring⟩
  have h6 : p ^ 6 ∣ s := hpd.dvd_of_dvd_mul_right h6s
  have h6' : p ^ 6 ∣ s * c := h6.mul_right c
  have h7 : p ^ 6 ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := h6'.trans hdvd
  have h8 : p ^ 3 ∣ (p ^ 2 - 1) * (p ^ 3 + 1) := by
    have : p ^ 3 * p ^ 3 ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
      rw [← pow_add]; exact h7
    exact (Nat.mul_dvd_mul_iff_left (by positivity)).mp this
  have hp_dvd : p ∣ (p ^ 2 - 1) * (p ^ 3 + 1) := (dvd_pow_self p (by norm_num)).trans h8
  rcases hp.dvd_mul.mp hp_dvd with h | h
  · have h1 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
    have h2 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h1 h
    have h3 : p ^ 2 - (p ^ 2 - 1) = 1 := by
      have := Nat.one_le_pow 2 p hp.pos
      omega
    rw [h3] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  · have h1 : p ∣ p ^ 3 := dvd_pow_self p (by norm_num)
    have h2 : p ∣ (p ^ 3 + 1) - p ^ 3 := Nat.dvd_sub h h1
    have h3 : (p ^ 3 + 1) - p ^ 3 = 1 := by omega
    rw [h3] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

end CFSG.Quasithin.A312U3

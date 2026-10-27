module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3SmArith
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3SmA7
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3SmNine
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3L3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Psu3Ord
public import CFSG.Quasithin.EmptyFaithful.T1515eC

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG.Quasithin

theorem psl2_q_cases_small {q s N : ℕ} (hq : 4 ≤ q) (ho : q % 2 = 1)
    (hN : N = 6048 ∨ N = 378000) (hs : 2 * s = q * (q ^ 2 - 1)) (h : s ∣ N) :
    (N = 6048 ∧ q = 7) ∨ (N = 378000 ∧ (q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 15)) := by
  rcases hN with rfl | rfl
  · exact Or.inl ⟨rfl, psl2_q_cases_6048 hq ho hs h⟩
  · exact Or.inr ⟨rfl, psl2_q_cases_378000 hq ho hs h⟩

theorem pow_ne_fifteen {r f : ℕ} (hr : r.Prime) (hf : 1 ≤ f) : r ^ f ≠ 15 := by
  intro h
  have hr2 := hr.two_le
  have hf2 : f ≤ 3 := by
    by_contra hf3
    push Not at hf3
    have : 2 ^ 4 ≤ r ^ f := (Nat.pow_le_pow_left hr2 4).trans (Nat.pow_le_pow_right (by omega) hf3)
    omega
  interval_cases f
  · rw [pow_one] at h
    subst h
    norm_num at hr
  · have : r ≤ 3 ∨ 4 ≤ r := by omega
    rcases this with h3 | h4
    · nlinarith
    · nlinarith
  · have : 2 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left hr2 3
    have h3 : r ≤ 2 ∨ 3 ≤ r := by omega
    rcases h3 with h3 | h3
    · interval_cases r; omega
    · have : 3 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left h3 3
      omega

variable {p : ℕ} {K : Type} [Field K] [Finite K] {M : Subgroup ↥(StatedSU 3 (p ^ 1) K)}
  {H : Subgroup (GL (Fin 3) K)}

theorem eq_top_of_psu3_card [Fact p.Prime] (hp3 : 3 ≤ p) (hK : Nat.card K = p ^ 2)
    (h : QCtx p K M H)
    (hs : Nat.card (H ⧸ Subgroup.center H) * Nat.gcd 3 (p + 1) =
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) : M = ⊤ := by
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have := charP_of_card_sq (p := p) hK
  have hperf : Group.IsPerfect ↥(StatedSU 3 (p ^ 1) K) :=
    CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd hK1 (n := 3) (by norm_num)
      (by intro h; simp at h; omega)
  exact eq_top_of_card_psu3 hperf h (Nat.gcd_dvd_left 3 _) (by rw [hs, card_su3_eq hK])

omit [Finite K] in
theorem two_dvd_mul_sq_sub_one {q : ℕ} (hq : Odd q) : 2 ∣ q * (q ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hq
  have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  rw [this]
  exact Dvd.dvd.mul_left ⟨2 * (k * (k + 1)), by ring⟩ _

theorem su3OddIrrSmall_holds
    : SU3OddIrrSmall := by
  intro p hpf hp35 K _ _ hK M hodd hirr
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have hoddK : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hK2 : (2 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_two hp2.symm
  rcases solvable_or_quasisimple_gl3 hirr with hsolv | ⟨H, hHG, hnorm, hq, hHirr, hscal, hdet, hZ⟩
  · right
    left
    exact Group.isSolvable_of_isSolvable_injective
      (f := (M.equivMapOfInjective _ (StatedSU 3 (p ^ 1) K).subtype_injective).toMonoidHom)
      (MulEquiv.injective _)
  · have hctx : QCtx p K M H := ⟨hodd, hHG, hnorm, hq, hHirr, hscal, hdet, hZ⟩
    obtain ⟨N, hNdef⟩ : ∃ N, N = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := ⟨_, rfl⟩
    have hNp : (N = 6048 ∧ p = 3) ∨ (N = 378000 ∧ p = 5) := by
      rcases hp35 with rfl | rfl
      · exact Or.inl ⟨by rw [hNdef]; norm_num, rfl⟩
      · exact Or.inr ⟨by rw [hNdef]; norm_num, rfl⟩
    have hN : N = 6048 ∨ N = 378000 := by
      rcases hNp with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    have hHdvd := card_dvd_of_qctx hK hctx
    rw [card_eq_quotient_mul H, ← hNdef] at hHdvd
    have hsN : Nat.card (H ⧸ Subgroup.center H) ∣ N := Dvd.dvd.trans (Dvd.intro _ rfl) hHdvd
    rcases quotient_center_rank_two_cases hoddK hq hdet hZ with
      ⟨r, f, hr, hr2, hf, hadm, K', _, _, hK', ⟨e⟩⟩ | ⟨r, f, hr, hr2, hf, -, K', _, _, hK', ⟨e⟩⟩ |
      ⟨r, f, hr, hr2, hf, -, K', _, _, hK', ⟨e⟩⟩ | ⟨-, K', _, _, hK', ⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩
    ·
      have hqodd : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
      have hq3 : r ^ f ≠ 3 := fun h => hadm.2.2.2.2 (by rw [h])
      have hq4 : 4 ≤ r ^ f := by
        by_contra hlt
        push Not at hlt
        obtain ⟨h1, h2⟩ := eq_three_of_pow_lt_four' hr hr2 hf hlt
        exact hq3 (by rw [h1, h2]; norm_num)
      have hs : 2 * Nat.card (H ⧸ Subgroup.center H) = r ^ f * ((r ^ f) ^ 2 - 1) := by
        rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL_two hqodd hK']
        exact Nat.mul_div_cancel' (two_dvd_mul_sq_sub_one hqodd)
      rcases psl2_q_cases_small hq4 (Nat.odd_iff.mp hqodd) hN hs hsN with
        ⟨-, h7⟩ | ⟨h378, h5 | h7 | h9 | h15⟩
      · exact (su3_not_psl2_prime hp2 hK hctx (r := 7) (by norm_num) (by norm_num)
          (by rw [hK', h7]) e).elim
      · exact (su3_not_psl2_prime hp2 hK hctx (r := 5) (by norm_num) (by norm_num)
          (by rw [hK', h5]) e).elim
      · exact (su3_not_psl2_prime hp2 hK hctx (r := 7) (by norm_num) (by norm_num)
          (by rw [hK', h7]) e).elim
      · have hp5 : p = 5 := by
          rcases hNp with ⟨h1, h2⟩ | ⟨-, h2⟩
          · omega
          · exact h2
        subst hp5
        have hK3 : (3 : K) ≠ 0 := by
          exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_three (by norm_num)
        obtain ⟨hHat, hsc⟩ := su3_nine_row hK3 hctx (F := K') (by rw [hK', h9]) e
        exact Or.inr (Or.inr ⟨rfl, hHat, hsc⟩)
      · exact (pow_ne_fifteen hr hf h15).elim
    ·
      have hqodd : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
      have hq3 : 3 ≤ r ^ f := by
        have := hr.two_le
        have h3 : 3 ≤ r := by
          rcases Nat.lt_or_ge r 3 with h | h
          · exact absurd (by omega : r = 2) hr2
          · exact h
        exact h3.trans (Nat.le_self_pow (by omega) r)
      let e' := e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K').symm
      have hpsl := card_psl3_mul_gcd (K := K')
      rw [hK'] at hpsl
      have hS : Nat.card (H ⧸ Subgroup.center H) =
          Nat.card (ProjectiveSpecialLinearGroup (Fin 3) K') := Nat.card_congr e'.toEquiv
      exact (psl3_false hq3 (Nat.odd_iff.mp hqodd) hN (by rw [hS]; exact hpsl) hsN).elim
    ·
      have hqodd : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
      have hq3 : 3 ≤ r ^ f := by
        have := hr.two_le
        have h3 : 3 ≤ r := by
          rcases Nat.lt_or_ge r 3 with h | h
          · exact absurd (by omega : r = 2) hr2
          · exact h
        exact h3.trans (Nat.le_self_pow (by omega) r)
      have hmul := CFSG.Quasithin.card_statedProj_statedSU_three_mul_gcd hr hf hK'
      have hS : Nat.card (H ⧸ Subgroup.center H) =
          Nat.card (StatedProj (StatedSU 3 (r ^ f) K')) := Nat.card_congr e.toEquiv
      generalize Nat.card (StatedProj (StatedSU 3 (r ^ f) K')) = n at hmul hS
      rw [← hS] at hmul
      have hres := psu3_small hq3 (Nat.odd_iff.mp hqodd) hN hmul hsN
      have hqp : r ^ f = p := by
        rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hNp with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
      rw [hqp] at hmul
      exact Or.inl (eq_top_of_psu3_card (by rcases hp35 with rfl | rfl <;> norm_num) hK hctx hmul)
    ·
      exact (false_of_psu34_K hK2 hdet hZ hK' e).elim
    ·
      obtain ⟨e⟩ := e
      exact (su3_not_alt7 hp2 hK hctx e).elim
    ·
      obtain ⟨e⟩ := e
      have h7920 : Nat.card (H ⧸ Subgroup.center H) = 7920 := by
        rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.GL2Recognition.card_lowTwoRankStatedM11]
      exact (not_dvd_7920 hN (h7920 ▸ hsN)).elim

end CFSG.Quasithin.A312U3

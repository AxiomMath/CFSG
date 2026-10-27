module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix

namespace SLRest

theorem pow_sub_pow_eq_mul {Q d i : ℕ} (h : i ≤ d) : Q ^ d - Q ^ i = Q ^ i * (Q ^ (d - i) - 1) := by
  rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' h]

theorem odd_prod_pow_sub_one {Q : ℕ} (hQ : Even Q) (hQ2 : 2 ≤ Q) (d : ℕ) :
    Odd (∏ i : Fin d, (Q ^ (d - (i : ℕ)) - 1)) := by
  refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i _ => ?_
  have hi : d - (i : ℕ) ≠ 0 := by have := i.2; omega
  have hev : Even (Q ^ (d - (i : ℕ))) := hQ.pow_of_ne_zero hi
  have hpos : 1 ≤ Q ^ (d - (i : ℕ)) := Nat.one_le_pow _ _ (by omega)
  exact Nat.Even.sub_odd hpos hev odd_one

theorem sum_fin_val (d : ℕ) : ∑ i : Fin d, (i : ℕ) = d * (d - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) d, ← Finset.sum_range_id_mul_two d,
    Nat.mul_div_cancel _ two_pos]

theorem card_GL_eq_pow_mul_odd {K : Type} [Field K] [Finite K] {Q : ℕ} (hK : Nat.card K = Q)
    (hQ : Even Q) (hQ2 : 2 ≤ Q) (d : ℕ) :
    ∃ u, Odd u ∧ Nat.card (GL (Fin d) K) = Q ^ (d * (d - 1) / 2) * u := by
  have : Fintype K := Fintype.ofFinite K
  refine ⟨_, odd_prod_pow_sub_one hQ hQ2 d, ?_⟩
  rw [Matrix.card_GL_field, Fintype.card_eq_nat_card, hK, ← sum_fin_val,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => pow_sub_pow_eq_mul i.2.le

theorem padicValNat_two_card_GL {K : Type} [Field K] [Finite K] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (he : 1 ≤ e) (d : ℕ) :
    padicValNat 2 (Nat.card (GL (Fin d) K)) = e * (d * (d - 1) / 2) := by
  have hQ : Even (2 ^ e) := even_two.pow_of_ne_zero (by omega)
  have hQ2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ e := Nat.pow_le_pow_right two_pos he
  obtain ⟨u, hu, hcard⟩ := card_GL_eq_pow_mul_odd hK hQ hQ2 d
  rw [hcard, ← pow_mul, padicValNat.mul (by positivity) hu.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)),
    add_zero]

theorem card_GL_congr {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (K : Type) [Field K] : Nat.card (GL ι K) = Nat.card (GL κ K) :=
  Nat.card_congr (Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toRingEquiv.toMulEquiv).toEquiv

theorem card_statedProj_dvd {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : Nat.card (StatedProj H) ∣ Nat.card (GL ι K) :=
  (Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm).trans
    (Subgroup.card_subgroup_dvd_card H)

theorem padicValNat_two_card_SL {K : Type} [Field K] [Finite K] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (he : 1 ≤ e) (d : ℕ) [NeZero d] :
    padicValNat 2 (Nat.card (SpecialLinearGroup (Fin d) K)) = e * (d * (d - 1) / 2) := by
  have : Fintype K := Fintype.ofFinite K
  have hGL := padicValNat_two_card_GL hK he d
  rw [Matrix.card_GL_field, Fintype.card_eq_nat_card, hK] at hGL
  have hQ1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hdvd : 2 ^ e - 1 ∣ ∏ i : Fin d, ((2 ^ e) ^ d - (2 ^ e) ^ (i : ℕ)) := by
    have h0 : (2 ^ e) ^ d - (2 ^ e) ^ ((0 : Fin d) : ℕ) ∣
        ∏ i : Fin d, ((2 ^ e) ^ d - (2 ^ e) ^ (i : ℕ)) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    refine dvd_trans ?_ h0
    rw [Fin.val_zero, pow_zero]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ e) d
  have hodd : ¬ 2 ∣ 2 ^ e - 1 := by
    have hev : Even (2 ^ e) := even_two.pow_of_ne_zero (by omega)
    have := Nat.Even.sub_odd hQ1 hev odd_one
    exact fun h => (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
  rw [Matrix.card_SL_field, Fintype.card_eq_nat_card, hK, padicValNat.div_of_dvd hdvd, hGL,
    padicValNat.eq_zero_of_not_dvd hodd, Nat.sub_zero]

theorem odd_card_center_SL {K : Type} [Field K] [Finite K] [CharP K 2] (d : ℕ) :
    Odd (Nat.card (Subgroup.center (SpecialLinearGroup (Fin d) K))) := by
  have : Fintype K := Fintype.ofFinite K
  by_contra h
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center
    (SpecialLinearGroup (Fin d) K)) 2 h
  have hz2 : ((z : SpecialLinearGroup (Fin d) K)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 := eq_one_of_mem_center_of_sq_eq_one z.2 hz2
  have : z = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem padicValNat_two_card_quotient_center {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    [CharP K 2] {e : ℕ} (hK : Nat.card K = 2 ^ e) (he : 1 ≤ e) {d : ℕ} [NeZero d]
    (eX : X ≃* SpecialLinearGroup (Fin d) K) :
    padicValNat 2 (Nat.card (X ⧸ Subgroup.center X)) = e * (d * (d - 1) / 2) := by
  have hX : Nat.card X = Nat.card (SpecialLinearGroup (Fin d) K) := Nat.card_congr eX.toEquiv
  have hZ : Nat.card (Subgroup.center X) =
      Nat.card (Subgroup.center (SpecialLinearGroup (Fin d) K)) :=
    Nat.card_congr (Subgroup.centerCongr eX).toEquiv
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  have hodd := odd_card_center_SL (K := K) d
  have hSL0 : Nat.card (SpecialLinearGroup (Fin d) K) ≠ 0 := Nat.card_pos.ne'
  rw [hX, hZ] at hsplit
  have hq0 : Nat.card (X ⧸ Subgroup.center X) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hsplit
    exact hSL0 hsplit
  have h := padicValNat_two_card_SL hK he d
  rw [hsplit, padicValNat.mul hq0 hodd.pos.ne',
    padicValNat.eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr h2)), add_zero] at h
  exact h

theorem padicValNat_two_le_of_dvd {X Y : Type} [Group X] [Group Y] (eXY : X ≃* Y) {M : ℕ}
    (hM : M ≠ 0) (hY : Nat.card Y ∣ M) : padicValNat 2 (Nat.card X) ≤ padicValNat 2 M := by
  rw [← padicValNat_dvd_iff_le hM]
  have hXY : Nat.card X = Nat.card Y := Nat.card_congr eXY.toEquiv
  rw [hXY]
  exact pow_padicValNat_dvd.trans hY

theorem card_GL_ne_zero {K : Type} [Field K] [Finite K] {e : ℕ} (hK : Nat.card K = 2 ^ e)
    (he : 1 ≤ e) (d : ℕ) : Nat.card (GL (Fin d) K) ≠ 0 := by
  have hQ : Even (2 ^ e) := even_two.pow_of_ne_zero (by omega)
  have hQ2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ e := Nat.pow_le_pow_right two_pos he
  obtain ⟨u, hu, hcard⟩ := card_GL_eq_pow_mul_odd hK hQ hQ2 d
  rw [hcard]
  exact mul_ne_zero (by positivity) hu.pos.ne'

theorem half_mul_pred_ne_of_mod_four {N : ℕ} (hN : N % 4 = 2) (k : ℕ) :
    N * (N - 1) / 2 ≠ k * (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, N = 4 * j + 2 := ⟨N / 4, by omega⟩
  have h1 : (4 * j + 2) * (4 * j + 2 - 1) / 2 = (2 * j + 1) * (4 * j + 1) := by
    rw [show 4 * j + 2 - 1 = 4 * j + 1 by omega,
      show (4 * j + 2) * (4 * j + 1) = 2 * ((2 * j + 1) * (4 * j + 1)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [h1]
  intro h
  have hodd : Odd ((2 * j + 1) * (4 * j + 1)) :=
    (odd_two_mul_add_one j).mul ⟨2 * j, by ring⟩
  rw [h] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_mul_pred_self k)

theorem eight_half_mul_pred_ne (k : ℕ) : 8 * (8 - 1) / 2 ≠ k * (k - 1) := by
  intro h
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k <;> simp_all
  · have : 6 * 5 ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
    omega

theorem not_ggSixSeventeenExcluded {G : Type} [Group G] {p f N : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) (hN : 6 ≤ N)
    (hpell : ∀ k : ℕ, N * (N - 1) / 2 ≠ k * (k - 1)) {L₁ : Subgroup G}
    (eL : L₁ ≃* SpecialLinearGroup (Fin N) F) : ¬ GGSixSeventeenExcluded p .PSL f L₁ := by
  have : NeZero N := ⟨by omega⟩
  have ha : padicValNat 2 (Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁)) = f * (N * (N - 1) / 2) :=
    padicValNat_two_card_quotient_center hF (by omega) eL
  have h15 : 15 ≤ N * (N - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le two_pos]
    have : 6 * 5 ≤ N * (N - 1) := Nat.mul_le_mul hN (by omega)
    omega
  have hf15 : f * 15 ≤ f * (N * (N - 1) / 2) := Nat.mul_le_mul_left f h15
  have hbound : ∀ {Y : Type} [Group Y] (_ : (↥L₁ ⧸ Subgroup.center ↥L₁) ≃* Y) {K : Type}
      [Field K] [Finite K] {e : ℕ} (_ : Nat.card K = 2 ^ e) (_ : 1 ≤ e) (d : ℕ)
      (_ : Nat.card Y ∣ Nat.card (GL (Fin d) K)),
      f * (N * (N - 1) / 2) ≤ e * (d * (d - 1) / 2) := by
    intro Y _ eY K _ _ e hK he d hY
    have := padicValNat_two_le_of_dvd eY (card_GL_ne_zero hK he d) hY
    rwa [ha, padicValNat_two_card_GL hK he d] at this
  rintro (⟨-, hU | hA | hO⟩ | ⟨-, hL2 | hO⟩ | ⟨-, -, hL2⟩ | ⟨ht, -⟩ | ⟨k, hk⟩)
  · rcases hU with ⟨-, -, K, _, _, hK, ⟨eY⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have := hbound eY (e := 2) (by rw [hK]; norm_num) (by norm_num) 4 (card_statedProj_dvd _)
      norm_num at this
      omega
    all_goals exact absurd h0 (by norm_num)
  · obtain ⟨eA⟩ := hA
    have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      rfl
    have := padicValNat_two_le_of_dvd eA (by norm_num : (360 : ℕ) ≠ 0) hcard.dvd
    have h360 : padicValNat 2 360 = 3 := by
      rw [show (360 : ℕ) = 2 ^ 3 * 45 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [ha, h360] at this
    omega
  · rcases hO with ⟨-, -, K, _, _, hK, ⟨eY⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have hdvd := card_statedProj_dvd (StatedOmega (StatedQuadPlus 4 K))
      rw [card_GL_congr (finSumFinEquiv (m := 4) (n := 4)) K] at hdvd
      have := hbound eY (e := 1) (by rw [hK]) le_rfl (4 + 4) hdvd
      norm_num at this
      omega
    all_goals exact absurd h0 (by norm_num)
  · rcases hL2 with ⟨-, -, K, _, _, hK, ⟨eY⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have := hbound eY (e := 2) hK (by norm_num) 2 (card_statedProj_dvd _)
      norm_num at this
      omega
    all_goals exact absurd h0 (by norm_num)
  · rcases hO with ⟨-, -, K, _, _, hK, ⟨eY⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have hdvd := card_statedProj_dvd (StatedOmega (StatedQuadPlus 4 K))
      rw [card_GL_congr (finSumFinEquiv (m := 4) (n := 4)) K] at hdvd
      have := hbound eY (e := 1) (by rw [hK]) le_rfl (4 + 4) hdvd
      norm_num at this
      omega
    all_goals exact absurd h0 (by norm_num)
  · rcases hL2 with ⟨-, -, K, _, _, hK, ⟨eY⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have := hbound eY hK (by omega) 2 (card_statedProj_dvd _)
      norm_num at this
      omega
    all_goals exact absurd h0 (by norm_num)
  · exact absurd ht (by decide)
  · rcases hk with ⟨-, hadm, K, _, _, hK, ⟨eY⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · obtain ⟨-, -, hk2, -, -⟩ := hadm
      have : NeZero k := ⟨by omega⟩
      have : Fintype K := Fintype.ofFinite K
      have : CharP K 2 :=
        charP_of_card_eq_prime_pow (f := 2 * f) (by rw [Fintype.card_eq_nat_card, hK])
      have eP := eY.trans (projectiveSpecialLinearGroupEquivStatedProj k K).symm
      have h1 : Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁) =
          Nat.card (SpecialLinearGroup (Fin k) K ⧸ Subgroup.center
            (SpecialLinearGroup (Fin k) K)) := Nat.card_congr eP.toEquiv
      have h2 := padicValNat_two_card_quotient_center hK (by omega) (MulEquiv.refl
        (SpecialLinearGroup (Fin k) K))
      rw [← h1, ha, show 2 * f * (k * (k - 1) / 2) = f * (2 * (k * (k - 1) / 2)) by ring,
        Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)] at h2
      exact hpell k (Nat.eq_of_mul_eq_mul_left (by omega) h2)
    all_goals exact absurd ht (by decide)

end SLRest

end CFSG.StandardType

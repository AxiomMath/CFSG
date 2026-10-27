module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofOddTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedProj StatedScalars)

namespace Item228Census2Proof

theorem card_projSL_two_of_odd {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    Nat.card (projSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
  have e : StatedProj (StatedSL 2 K) ≃* projSL 2 K :=
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSL 2 K)).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSL 2 K))
  rw [← Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2) (by norm_num)]
  have hg : Nat.gcd 2 (Nat.card K - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  rw [hg, show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton]
  norm_num

theorem dvd_or_dvd_of_isPrimePow {q a b : ℕ} (hq : IsPrimePow q) (hab : Nat.Coprime a b)
    (h : q ∣ a * b) : q ∣ a ∨ q ∣ b := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have hpab : p ∣ a * b := (dvd_pow_self p hk.ne').trans h
  rcases (Nat.Prime.dvd_mul hp').mp hpab with hpa | hpb
  · left
    have hpb : ¬ p ∣ b := fun hpb =>
      hp'.ne_one (Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hab ▸ Nat.dvd_gcd hpa hpb))
    exact (Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd hp').mpr hpb)).dvd_of_dvd_mul_right h
  · right
    have hpa : ¬ p ∣ a := fun hpa =>
      hp'.ne_one (Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hab ▸ Nat.dvd_gcd hpa hpb))
    exact (Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd hp').mpr hpa)).dvd_of_dvd_mul_left h

theorem psl2_card_ne {q : ℕ} (hq : IsPrimePow q) (hodd : Odd q) (h7 : 7 ≤ q) :
    (∀ m : ℕ, 0 < m → q * (q ^ 2 - 1) / 2 ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1)) ∧
      q * (q ^ 2 - 1) / 2 ≠ 62400 := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have heven : 2 ∣ q * (q ^ 2 - 1) := by
    obtain ⟨k, rfl⟩ := hodd
    refine Dvd.dvd.mul_left ?_ _
    refine ⟨2 * k ^ 2 + 2 * k, ?_⟩
    have : 1 ≤ (2 * k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this]
    ring
  have hdouble : ∀ N, q * (q ^ 2 - 1) / 2 = N → q * (q ^ 2 - 1) = 2 * N := by
    intro N hN
    rw [← hN]
    exact (Nat.mul_div_cancel' heven).symm
  refine ⟨fun m hm hN => ?_, fun hN => ?_⟩
  · have h1 := hdouble _ hN
    set s := 2 ^ m with hs
    have hs2 : 2 ≤ s := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hs1 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hsq : s ^ 2 - 1 = (s - 1) * (s + 1) := by
      zify [hs1, show 1 ≤ s by omega]
      ring
    have hcop2 : Nat.Coprime q (2 * s) := by
      have : Nat.Coprime q 2 := Nat.coprime_two_right.mpr hodd
      rw [hs, ← pow_succ']
      exact Nat.Coprime.pow_right _ this
    have hdvd : q ∣ (s - 1) * (s + 1) := by
      have : q ∣ 2 * s * ((s - 1) * (s + 1)) := by
        rw [← hsq, mul_assoc, ← h1]
        exact Dvd.intro _ rfl
      exact hcop2.dvd_of_dvd_mul_left this
    have hcop : Nat.Coprime (s - 1) (s + 1) := by
      have hodd1 : Odd (s - 1) := by
        rw [hs]
        exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, hm.ne'⟩) odd_one
      set g := Nat.gcd (s - 1) (s + 1) with hg
      have hg1 : g ∣ s - 1 := Nat.gcd_dvd_left _ _
      have hg2 : g ∣ s + 1 := Nat.gcd_dvd_right _ _
      have hg3 : g ∣ 2 := by
        have : s + 1 - (s - 1) = 2 := by omega
        rw [← this]
        exact Nat.dvd_sub hg2 hg1
      rcases (Nat.dvd_prime Nat.prime_two).mp hg3 with h | h
      · exact h
      · exfalso
        rw [h] at hg1
        obtain ⟨k, hk⟩ := hodd1
        omega
    have hqs : q ≤ s + 1 := by
      rcases dvd_or_dvd_of_isPrimePow hq hcop hdvd with h | h
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
      · exact Nat.le_of_dvd (by omega) h
    have hmono : q * (q ^ 2 - 1) ≤ (s + 1) * ((s + 1) ^ 2 - 1) :=
      Nat.mul_le_mul hqs (Nat.sub_le_sub_right (Nat.pow_le_pow_left hqs 2) 1)
    have hlow : 336 ≤ q * (q ^ 2 - 1) :=
      calc 336 = 7 * (7 ^ 2 - 1) := by norm_num
        _ ≤ q * (q ^ 2 - 1) :=
          Nat.mul_le_mul h7 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h7 2) 1)
    rw [h1] at hmono hlow
    have hs1' : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hs1, hs1'] at hmono hlow
    nlinarith
  · have h1 := hdouble _ hN
    have hq50 : q < 50 := by
      by_contra hge
      push Not at hge
      have : 50 * (50 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hge (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1)
      omega
    interval_cases q <;> omega

theorem noL2Config228_projSL_two {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h7 : 7 ≤ Nat.card K) : NoL2Config228 (projSL 2 K) := by
  have hpp : IsPrimePow (Nat.card K) := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card K
  have : IsSimpleGroup (projSL 2 K) := by
    have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := K) 2 le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
    exact (Sec4.projSLEquivPSLn 2 K).isSimpleGroup
  have : Finite (projSL 2 K) :=
    Finite.of_equiv _ (Sec4.projSLEquivPSLn 2 K).symm.toEquiv
  obtain ⟨hne1, hne2⟩ := psl2_card_ne hpp hodd h7
  refine noL2Config228_of_simple (fun m hm _ => ?_) ?_
  · rw [card_projSL_two_of_odd hodd, card_projSL_two m hm]
    exact hne1 m hm
  · rw [card_projSL_two_of_odd hodd]
    exact hne2

end Item228Census2Proof

end CFSG.RankThree.PartTwo.Sec21

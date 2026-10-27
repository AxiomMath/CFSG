module

public import CFSG.OddTranspositions.O4Minus5Pair
public import CFSG.Dihedral.GorensteinWalter.ExternalSimpleAdapter
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem

public section

noncomputable section

namespace CFSG.OddTranspositions

open QZ

open CFSG.GorensteinWalter

theorem nonempty_mulEquiv_psl225_of_card
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (hcard : Nat.card L = 7800)
    (hdih : CFSG.GorensteinWalter.HasDihedralSylowTwo L) : Nonempty (L ≃* PSL225) := by
  classical
  have hnonab : ∃ a b : L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    haveI : IsMulCommutative L := isMulCommutative_iff.mpr h
    have hprime : (Nat.card L).Prime :=
      (Group.is_simple_iff_prime_card (α := L)).mp inferInstance
    rw [hcard] at hprime
    exact (by norm_num : ¬ (7800 : ℕ).Prime) hprime
  let P : Sylow 2 L := Classical.choice Sylow.nonempty
  have hdih' : ∃ n : ℕ, Nonempty ((P : Subgroup L) ≃* DihedralGroup n) := by
    obtain ⟨m, -, he⟩ := hdih P
    exact ⟨2 ^ m, he⟩
  have hD : CFSG.GorensteinWalter.IsDGroup L :=
    CFSG.GorensteinWalter.gorensteinWalter L hdih
  rcases CFSG.GorensteinWalter.ExternalSimpleAdapter.conclusion_of_isDGroup L hnonab P hdih' hD
    with h7 | ⟨p, k, hp, hpodd, hpk, e⟩
  · obtain ⟨e7⟩ := h7
    have hc7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hcard7 : Nat.card L = 2520 := by rw [Nat.card_congr e7.toEquiv, hc7]
    omega
  · obtain ⟨e⟩ := e
    let q : ℕ := Nat.card (GaloisField p k)
    haveI : Fact p.Prime := hp
    have hk0 : k ≠ 0 := by
      intro hk
      rw [hk, pow_zero] at hpk
      omega
    have hqcard : q = p ^ k := GaloisField.card p k hk0
    have hoddq : CFSG.GorensteinWalter.IsOddPrimePower q :=
      ⟨p, k, hp.out, hpodd, Nat.one_le_iff_ne_zero.mpr hk0, hqcard⟩
    have hqformula : Nat.card (PSL2 (GaloisField p k)) = q * (q ^ 2 - 1) / 2 :=
      CFSG.GorensteinWalter.psl2_card_formula (GaloisField p k) hoddq
    have hqeq : q * (q ^ 2 - 1) / 2 = 7800 := by
      rw [← hqformula, ← Nat.card_congr e.toEquiv, hcard]
    have hqodd : Odd q := by rw [hqcard]; exact hpodd.pow
    have hq25 : q = 25 := by
      have hmono : ∀ a b : ℕ, a ≤ b →
          a * (a ^ 2 - 1) / 2 ≤ b * (b ^ 2 - 1) / 2 := by
        intro a b hab
        exact Nat.div_le_div_right (Nat.mul_le_mul hab
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hab 2) 1))
      have h25q : 25 ≤ q := by
        by_contra hlt
        have h24 : q ≤ 24 := by omega
        obtain ⟨m, hm⟩ := hqodd
        have hq23 : q ≤ 23 := by omega
        have hmono23 := hmono q 23 hq23
        have h23 : 23 * (23 ^ 2 - 1) / 2 = 6072 := by norm_num
        rw [hqeq, h23] at hmono23
        omega
      have hq25le : q ≤ 25 := by
        by_contra hlt
        have h26 : 26 ≤ q := by omega
        have hmono26 := hmono 26 q h26
        have h26v : 26 * (26 ^ 2 - 1) / 2 = 8775 := by norm_num
        rw [h26v, hqeq] at hmono26
        omega
      omega
    have hpk25 : p ^ k = 25 := hqcard ▸ hq25
    have hp_dvd : p ∣ 25 := by
      rw [← hpk25]
      exact dvd_pow_self p hk0
    have hp_dvd5 : p ∣ 5 := by
      have h : p ∣ 5 ^ 2 := by
        rwa [show (5 : ℕ) ^ 2 = 25 by norm_num]
      exact hp.out.dvd_of_dvd_pow h
    have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_five).mp hp_dvd5
    subst p
    have hk2 : k = 2 := by
      have h25 : (25 : ℕ) = 5 ^ 2 := by norm_num
      exact Nat.pow_right_injective (show 1 < 5 by norm_num) (hpk25.trans h25)
    subst k
    exact ⟨e⟩

end CFSG.OddTranspositions

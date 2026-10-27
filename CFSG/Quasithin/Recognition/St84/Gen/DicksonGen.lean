module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.Sylow
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.Quasithin.Recognition.St84.L2Group
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

public section

namespace CFSG.Quasithin.St84

open CFSG.Glauberman.Dickson

private abbrev P2 (n : ℕ) :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)

private lemma odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  have hEven : Even (2 ^ n) := Even.pow_of_ne_zero even_two (by omega)
  exact Nat.Even.sub_odd Nat.one_le_two_pow hEven odd_one

private lemma odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) :=
  Even.add_odd (Even.pow_of_ne_zero even_two (by omega)) odd_one

private lemma gcd_two_pow_sub_one_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.gcd (2 ^ n - 1) 2 = 1 :=
  Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr (odd_two_pow_sub_one hn))

private lemma odd_div_gcd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) :
    Odd ((2 ^ n - 1) / Nat.gcd (2 ^ n - 1) 2) := by
  rw [gcd_two_pow_sub_one_two hn, Nat.div_one]
  exact odd_two_pow_sub_one hn

private lemma odd_div_gcd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) :
    Odd ((2 ^ n + 1) / Nat.gcd (2 ^ n - 1) 2) := by
  rw [gcd_two_pow_sub_one_two hn, Nat.div_one]
  exact odd_two_pow_add_one hn

private lemma dvd_card_of_isPGroup_two {G : Type*} [Group G] {A : Subgroup G} [Finite A]
    {m : ℕ} (hA2 : IsPGroup 2 A) (hAc : 2 ^ m ≤ Nat.card A) : 2 ^ m ∣ Nat.card A := by
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  rw [hk] at hAc ⊢
  exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp hAc)

private lemma ne_bot_of_large_two_pow {n : ℕ} (hn : 3 ≤ n)
    {G : Type*} [Group G] {A : Subgroup G}
    (hAc : 2 ^ (n - 1) ≤ Nat.card A) : A ≠ ⊥ := by
  intro hbot
  have h4 : 4 ≤ 2 ^ (n - 1) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hbot, Subgroup.card_bot] at hAc
  omega

theorem psl2_eq_top_of_large_two_subgroup {n : ℕ} (hn : 3 ≤ n)
    {H A B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))}
    (hA : A ≤ H) (hB : B ≤ H) (hA2 : IsPGroup 2 A) (hB2 : IsPGroup 2 B)
    (hAc : 2 ^ (n - 1) ≤ Nat.card A) (hAB : ¬ IsPGroup 2 ↥(A ⊔ B)) : H = ⊤ := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hn1 : 1 ≤ n := by omega
  have hq : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hAdvdH : Nat.card A ∣ Nat.card H := Subgroup.card_dvd_of_le hA
  have h4le : 2 ^ 2 ≤ Nat.card A := by
    calc
      2 ^ 2 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ Nat.card A := hAc
  have hA4 : 4 ∣ Nat.card A := by
    have h := dvd_card_of_isPGroup_two hA2 h4le
    simpa using h
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 2) (f := n) hq H with
    hEl | ⟨z, hzdiv, hzcard, _hzcyc⟩ | ⟨z, hzdiv, hzcard, _hzdi⟩ |
      ⟨hA4c, hA4iso⟩ | ⟨h16, _hS4⟩ | ⟨h5, hA5⟩ |
      ⟨m, t, _ht1, ht2, N, C, hNnorm, hNel, hNcard, _hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmdiv, hPSL⟩ | ⟨m, hm0, hm2div, hPGL⟩
  ·
    exfalso
    haveI : IsElementaryAbelian 2 H := hEl
    exact hAB ((IsElementaryAbelian.isPGroup 2 H).to_le (sup_le hA hB))
  ·
    exfalso
    rw [hq] at hzdiv
    have hzodd : Odd z := hzdiv.elim
      (fun h => Odd.of_dvd_nat (odd_div_gcd_two_pow_sub_one hn1) h)
      (fun h => Odd.of_dvd_nat (odd_div_gcd_two_pow_add_one hn1) h)
    have h4z : 4 ∣ z := by
      rw [← hzcard]
      exact hA4.trans hAdvdH
    exact (Nat.not_even_iff_odd.mpr hzodd) (Dvd.dvd.even h4z (by norm_num : Even 4))
  ·
    exfalso
    rw [hq] at hzdiv
    have hzodd : Odd z := hzdiv.elim
      (fun h => Odd.of_dvd_nat (odd_div_gcd_two_pow_sub_one hn1) h)
      (fun h => Odd.of_dvd_nat (odd_div_gcd_two_pow_add_one hn1) h)
    have h4H : 4 ∣ Nat.card H := hA4.trans hAdvdH
    rw [hzcard] at h4H
    obtain ⟨c, hc⟩ := h4H
    obtain ⟨k, hk⟩ := hzodd
    omega
  ·
    exfalso
    have hnEven : Even n := by
      rcases hA4c with hp2 | hf
      · exact absurd rfl hp2
      · exact hf
    obtain ⟨eA4⟩ := hA4iso
    have hH12 : Nat.card H = 12 := by
      rw [Nat.card_congr eA4.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    obtain ⟨k, hk⟩ := hnEven
    have h8A : 8 ∣ Nat.card A := by
      have h8le : 2 ^ 3 ≤ Nat.card A := by
        calc
          2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ Nat.card A := hAc
      have h := dvd_card_of_isPGroup_two hA2 h8le
      simpa using h
    have h8H : 8 ∣ Nat.card H := h8A.trans hAdvdH
    rw [hH12] at h8H
    norm_num at h8H
  ·
    exfalso
    have hEven : Even (2 ^ (2 * n) - 1) :=
      Dvd.dvd.even h16 (by norm_num : Even 16)
    have hOdd : Odd (2 ^ (2 * n) - 1) := by
      have hEvenPow : Even (2 ^ (2 * n)) := Even.pow_of_ne_zero even_two (by omega)
      exact Nat.Even.sub_odd Nat.one_le_two_pow hEvenPow odd_one
    exact (Nat.not_even_iff_odd.mpr hOdd) hEven
  ·
    exfalso
    obtain ⟨eA5⟩ := hA5
    have hH60 : Nat.card H = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have h5dvd : 5 ∣ 2 ^ (2 * n) - 1 := by
      rcases h5 with hp5 | h5d
      · exact absurd hp5 (by norm_num)
      · exact h5d
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    have h2k_dvd : 2 ^ k ∣ 60 := by
      rw [← hk]
      rw [hH60] at hAdvdH
      exact hAdvdH
    have hk_le : k ≤ 2 := by
      have hcop : Nat.Coprime (2 ^ k) 15 := (by norm_num : Nat.Coprime 2 15).pow_left k
      have h4 : 2 ^ k ∣ 4 * 15 := by
        rw [show 4 * 15 = 60 by norm_num]
        exact h2k_dvd
      have hdvd4 : 2 ^ k ∣ 4 := hcop.dvd_of_dvd_mul_right h4
      have hdvd4' : 2 ^ k ∣ 2 ^ 2 := by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
        exact hdvd4
      exact (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp hdvd4'
    have hnle : n ≤ 3 := by
      have hnk : n - 1 ≤ k :=
        (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by rwa [hk] at hAc)
      omega
    have hn3 : n = 3 := by omega
    rw [hn3] at h5dvd
    norm_num at h5dvd
  ·
    exfalso
    have htodd : Odd t := Odd.of_dvd_nat (odd_div_gcd_two_pow_sub_one hn1) ht2
    haveI : N.Normal := hNnorm
    haveI : IsElementaryAbelian 2 N := hNel
    have hN2 : IsPGroup 2 N := IsElementaryAbelian.isPGroup 2 N
    have hcompl : N.IsComplement' C := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
      rw [← Subgroup.normal_mul N C, hsup]
      rfl
    have hcardH : Nat.card H = Nat.card N * Nat.card C := hcompl.card_mul_card.symm
    have hNindex : N.index = t := by
      have h1 : N.index * Nat.card N = Nat.card H := N.index_mul_card
      rw [hcardH, hNcard, hCcard, mul_comm (2 ^ m) t] at h1
      exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0 : ℕ) < 2) m) h1
    let Nsyl : Sylow 2 H := hN2.toSylow (by rw [hNindex]; exact htodd.not_two_dvd_nat)
    have hA2' : IsPGroup 2 (A.subgroupOf H) :=
      hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm
    have hB2' : IsPGroup 2 (B.subgroupOf H) :=
      hB2.of_equiv (Subgroup.subgroupOfEquivOfLe hB).symm
    have le_of_le_sylow : (A.subgroupOf H) ≤ N ∧ (B.subgroupOf H) ≤ N := by
      constructor
      · obtain ⟨Q, hAQ⟩ := hA2'.exists_le_sylow
        have hNQ : N ≤ (Q : Subgroup H) := IsPGroup.le_sylow_of_normal hN2 Q
        have hQN : (Q : Subgroup H) = N := Nsyl.is_maximal' Q.isPGroup' hNQ
        exact hQN ▸ hAQ
      · obtain ⟨Q, hBQ⟩ := hB2'.exists_le_sylow
        have hNQ : N ≤ (Q : Subgroup H) := IsPGroup.le_sylow_of_normal hN2 Q
        have hQN : (Q : Subgroup H) = N := Nsyl.is_maximal' Q.isPGroup' hNQ
        exact hQN ▸ hBQ
    have hAimage : A ≤ N.map H.subtype := by
      have hmap : (A.subgroupOf H).map H.subtype ≤ N.map H.subtype :=
        Subgroup.map_mono le_of_le_sylow.1
      rwa [Subgroup.map_subgroupOf_eq_of_le hA] at hmap
    have hBimage : B ≤ N.map H.subtype := by
      have hmap : (B.subgroupOf H).map H.subtype ≤ N.map H.subtype :=
        Subgroup.map_mono le_of_le_sylow.2
      rwa [Subgroup.map_subgroupOf_eq_of_le hB] at hmap
    have hNimage2 : IsPGroup 2 (N.map H.subtype) := by
      haveI : IsElementaryAbelian 2 (N.map H.subtype) := hNel.map_subtype
      exact IsElementaryAbelian.isPGroup 2 (N.map H.subtype)
    exact hAB (hNimage2.to_le (sup_le hAimage hBimage))
  ·
    obtain ⟨e⟩ := hPSL
    have hHcard : Nat.card H = Nat.card (P2 m) := Nat.card_congr e.toEquiv
    have hPSLcard : Nat.card (P2 m) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      simpa using CFSG.Walter.psl2_even_card (f := m) hm0
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    have hodd : Odd ((2 ^ m) ^ 2 - 1) := by
      have hEven : Even ((2 ^ m) ^ 2) :=
        (Even.pow_of_ne_zero even_two hm0).pow_of_ne_zero (by norm_num : 2 ≠ 0)
      have h1 : 1 ≤ (2 ^ m) ^ 2 :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (pow_ne_zero m (by norm_num)))
      exact Nat.Even.sub_odd h1 hEven odd_one
    have hk_dvd : 2 ^ k ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [hk, hHcard, hPSLcard] at hAdvdH
      exact hAdvdH
    have hcop : Nat.Coprime (2 ^ k) ((2 ^ m) ^ 2 - 1) :=
      (Nat.coprime_two_left.mpr hodd).pow_left k
    have hkm : k ≤ m :=
      (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hk_dvd)
    have hnk : n - 1 ≤ k :=
      (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by rwa [hk] at hAc)
    have hmn : m ≤ n := Nat.le_of_dvd (by omega) hmdiv
    have hm_eq : m = n := by
      by_contra hne
      have hmlt : m < n := lt_of_le_of_ne hmn hne
      have hmsub : m = n - 1 := by omega
      have hdvd1 : m ∣ 1 := by
        have hsub : n - (n - 1) = 1 := by omega
        have h : m ∣ n - (n - 1) := Nat.dvd_sub hmdiv (by rw [← hmsub])
        rwa [hsub] at h
      have hm1 : m = 1 := Nat.dvd_one.mp hdvd1
      omega
    refine Subgroup.eq_top_of_card_eq H ?_
    rw [hHcard, hPSLcard, hm_eq]
    exact (CFSG.Walter.psl2_even_card (f := n) hn0).symm
  ·
    exfalso
    obtain ⟨e⟩ := hPGL
    have hHcard : Nat.card H = Nat.card (Matrix.ProjGenLinGroup (Fin 2)
        (GaloisField 2 m)) := Nat.card_congr e.toEquiv
    have hPGLcard : Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) =
        2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      simpa [GaloisField.card 2 m hm0] using
        CFSG.BenderSuzuki.External.huppertXI13_card_pgl2 (K := GaloisField 2 m)
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    have hodd : Odd ((2 ^ m) ^ 2 - 1) := by
      have hEven : Even ((2 ^ m) ^ 2) :=
        (Even.pow_of_ne_zero even_two hm0).pow_of_ne_zero (by norm_num : 2 ≠ 0)
      have h1 : 1 ≤ (2 ^ m) ^ 2 :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (pow_ne_zero m (by norm_num)))
      exact Nat.Even.sub_odd h1 hEven odd_one
    have hk_dvd : 2 ^ k ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [hk, hHcard, hPGLcard] at hAdvdH
      exact hAdvdH
    have hcop : Nat.Coprime (2 ^ k) ((2 ^ m) ^ 2 - 1) :=
      (Nat.coprime_two_left.mpr hodd).pow_left k
    have hkm : k ≤ m :=
      (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hk_dvd)
    have hnk : n - 1 ≤ k :=
      (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp (by rwa [hk] at hAc)
    have hm2n : 2 * m ≤ n := Nat.le_of_dvd (by omega) hm2div
    omega

theorem psl2_eq_top_of_sylow_ne {n : ℕ} (hn : 3 ≤ n)
    {H A B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))}
    {P P' : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))}
    (hPP' : P ≠ P') (hAP : A ≤ P) (hBP : B ≤ P') (hA : A ≤ H) (hB : B ≤ H)
    (hAc : 2 ^ (n - 1) ≤ Nat.card A) (hB1 : B ≠ ⊥) : H = ⊤ := by
  have hA2 : IsPGroup 2 A := P.isPGroup'.to_le hAP
  have hB2 : IsPGroup 2 B := P'.isPGroup'.to_le hBP
  refine psl2_eq_top_of_large_two_subgroup hn hA hB hA2 hB2 hAc ?_
  intro hAB2
  obtain ⟨Q, hQ⟩ := hAB2.exists_le_sylow
  have hAQ : A ≤ (Q : Subgroup (P2 n)) := le_sup_left.trans hQ
  have hBQ : B ≤ (Q : Subgroup (P2 n)) := le_sup_right.trans hQ
  have hA1 : A ≠ ⊥ := ne_bot_of_large_two_pow hn hAc
  have hPQ : P = Q := by
    by_contra hne
    have hti := psl2_ti (f := n) (by omega) hne
    have hAle : A ≤ (⊥ : Subgroup (P2 n)) := by
      rw [← hti]
      exact le_inf hAP hAQ
    exact hA1 (le_bot_iff.mp hAle)
  have hP'Q : P' = Q := by
    by_contra hne
    have hti := psl2_ti (f := n) (by omega) hne
    have hBle : B ≤ (⊥ : Subgroup (P2 n)) := by
      rw [← hti]
      exact le_inf hBP hBQ
    exact hB1 (le_bot_iff.mp hBle)
  exact hPP' (hPQ.trans hP'Q.symm)

end CFSG.Quasithin.St84

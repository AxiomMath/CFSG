module

import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.Dihedral.Glauberman.DicksonMaxUp

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Glauberman.Dickson BenderSuzuki.MatrixGroups

namespace Res8

theorem ne_zero_of_card_eq_two_pow {F : Type} [Field F] [Finite F] {j : ℕ}
    (hF : Nat.card F = 2 ^ j) : j ≠ 0 := by
  rintro rfl
  have : Fintype F := Fintype.ofFinite F
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  rw [← Nat.card_eq_fintype_card, hF, pow_zero] at h1
  exact lt_irrefl 1 h1

theorem exists_card_eq_of_elementaryAbelian {p : ℕ} [Fact p.Prime] {X : Type*} [Group X]
    [Finite X] (h : IsElementaryAbelian p X) : ∃ a : ℕ, Nat.card X = p ^ a :=
  (IsElementaryAbelian.isPGroup p X).exists_card_eq

theorem card_le_of_odd_psl2_char_two {F : Type} [Field F]
    [Finite F] {j : ℕ} (hF : Nat.card F = 2 ^ j) (C : Subgroup (PSL2MatrixGroup F))
    (hodd : Odd (Nat.card C)) : Nat.card C ≤ 2 ^ j + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hj := ne_zero_of_card_eq_two_pow hF
  have hpos : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hj)
  have hgcd : Nat.gcd (2 ^ j - 1) 2 = 1 := by
    have hodd' : Odd (2 ^ j - 1) := by
      have h2 : Even (2 ^ j) := (Nat.even_pow' hj).mpr even_two
      obtain ⟨r, hr⟩ := h2
      exact ⟨r - 1, by omega⟩
    exact Nat.Coprime.symm (Nat.coprime_two_left.mpr hodd')
  have hnot2 : ¬ 2 ∣ Nat.card C := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification (p := 2) hF C with
    hEA | ⟨z, hz, hzc, -⟩ | ⟨z, -, hzc, -⟩ | ⟨-, ⟨ha4⟩⟩ | ⟨-, ⟨hs4⟩⟩ | ⟨-, ⟨ha5⟩⟩ |
      ⟨m', t, -, ht, N₀, C₀, -, hN₀e, hN₀c, -, hC₀c, -, hN₀C₀⟩ | ⟨m', hm', -, ⟨e⟩⟩ |
      ⟨m', hm', -, ⟨e⟩⟩
  · obtain ⟨a, ha⟩ := exists_card_eq_of_elementaryAbelian hEA
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [ha, h0, pow_zero]
      omega
    · exact absurd (ha ▸ dvd_pow_self 2 h0.ne') hnot2
  · rw [hF, hgcd, Nat.div_one, Nat.div_one] at hz
    rw [hzc]
    rcases hz with h | h
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h
  · exact absurd (hzc ▸ dvd_mul_right 2 z) hnot2
  · have h12 : Nat.card C = 12 := by
      rw [Nat.card_congr ha4.toEquiv, nat_card_alternatingGroup]
      simp [Nat.card_eq_fintype_card]
      rfl
    exact absurd (h12 ▸ (by norm_num : 2 ∣ 12)) hnot2
  · have h24 : Nat.card C = 24 := by
      rw [Nat.card_congr hs4.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    exact absurd (h24 ▸ (by norm_num : 2 ∣ 24)) hnot2
  · have h60 : Nat.card C = 60 := by
      rw [Nat.card_congr ha5.toEquiv, nat_card_alternatingGroup]
      simp [Nat.card_eq_fintype_card]
      rfl
    exact absurd (h60 ▸ (by norm_num : 2 ∣ 60)) hnot2
  ·
    have hN₀dvd : Nat.card N₀ ∣ Nat.card C := by
      rw [← Subgroup.card_top (G := ↥C)]
      exact Subgroup.card_dvd_of_le le_top
    have hm0 : m' = 0 := by
      by_contra hne
      exact hnot2 ((hN₀c ▸ dvd_pow_self 2 hne).trans hN₀dvd)
    have hN₀bot : N₀ = ⊥ := by
      rw [← Subgroup.card_eq_one, hN₀c, hm0, pow_zero]
    rw [hN₀bot, bot_sup_eq] at hN₀C₀
    have hCt : Nat.card C = t := by
      rw [← hC₀c, hN₀C₀, Subgroup.card_top]
    rw [hgcd, Nat.div_one] at ht
    rw [hCt]
    exact (Nat.le_of_dvd (by omega) ht).trans (by omega)
  · have h2 : 2 ∣ Nat.card C := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.two_dvd_natCard_psl2 _
    exact absurd h2 hnot2
  · have h2 : 2 ∣ Nat.card C := by
      rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula,
        GaloisField.card 2 m' hm']
      exact Dvd.dvd.mul_right (dvd_pow_self 2 hm') _
    exact absurd h2 hnot2

theorem card_le_five_of_odd_psl2_five [Fact (Nat.Prime 5)]
    (C : Subgroup (PSL2MatrixGroup (GaloisField 5 1))) (hodd : Odd (Nat.card C)) :
    Nat.card C ≤ 5 := by
  have hF : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
  have hP : Nat.card (PSL2MatrixGroup (GaloisField 5 1)) = 60 :=
    (MaxUp.card_psl2_galoisField (p := 5) (m := 1) (by norm_num) one_ne_zero).trans
      (by norm_num)
  have hCdvd : Nat.card C ∣ 60 := hP ▸ Subgroup.card_subgroup_dvd_card C
  have hnot2 : ¬ 2 ∣ Nat.card C := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hpow : ∀ a : ℕ, 5 ^ a ∣ 60 → 5 ^ a ≤ 5 := by
    intro a ha
    rcases Nat.lt_or_ge a 2 with h | h
    · interval_cases a <;> norm_num
    · exfalso
      have : 25 ∣ 60 := (pow_dvd_pow 5 h).trans ha
      norm_num at this
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification (p := 5) hF C with
    hEA | ⟨z, hz, hzc, -⟩ | ⟨z, -, hzc, -⟩ | ⟨-, ⟨ha4⟩⟩ | ⟨-, ⟨hs4⟩⟩ | ⟨-, ⟨ha5⟩⟩ |
      ⟨m', t, -, ht, N₀, C₀, -, hN₀e, hN₀c, -, hC₀c, -, hN₀C₀⟩ | ⟨m', hm', hm'1, ⟨e⟩⟩ |
      ⟨m', hm', hm'1, -⟩
  · obtain ⟨a, ha⟩ := exists_card_eq_of_elementaryAbelian hEA
    rw [ha] at hCdvd ⊢
    exact hpow a hCdvd
  · rw [hF] at hz
    norm_num at hz
    rw [hzc]
    rcases hz with h | h
    · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
    · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
  · exact absurd (hzc ▸ dvd_mul_right 2 z) hnot2
  · have h12 : Nat.card C = 12 := by
      rw [Nat.card_congr ha4.toEquiv, nat_card_alternatingGroup]
      simp [Nat.card_eq_fintype_card]
      rfl
    exact absurd (h12 ▸ (by norm_num : 2 ∣ 12)) hnot2
  · have h24 : Nat.card C = 24 := by
      rw [Nat.card_congr hs4.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    exact absurd (h24 ▸ (by norm_num : 2 ∣ 24)) hnot2
  · have h60 : Nat.card C = 60 := by
      rw [Nat.card_congr ha5.toEquiv, nat_card_alternatingGroup]
      simp [Nat.card_eq_fintype_card]
      rfl
    exact absurd (h60 ▸ (by norm_num : 2 ∣ 60)) hnot2
  ·
    norm_num at ht
    have hC₀dvd : Nat.card C₀ ∣ Nat.card C := by
      rw [← Subgroup.card_top (G := ↥C)]
      exact Subgroup.card_dvd_of_le le_top
    have ht1 : t = 1 := by
      rw [hC₀c] at hC₀dvd
      have hto : ¬ 2 ∣ t := fun h2 => hnot2 (h2.trans hC₀dvd)
      have := Nat.le_of_dvd (by norm_num) ht
      interval_cases t
      · simp at ht
      · rfl
      · exact absurd (dvd_refl 2) hto
    have hC₀bot : C₀ = ⊥ := by rw [← Subgroup.card_eq_one, hC₀c, ht1]
    rw [hC₀bot, sup_bot_eq] at hN₀C₀
    have hCN : Nat.card C = 5 ^ m' := by rw [← hN₀c, hN₀C₀, Subgroup.card_top]
    rw [hCN] at hCdvd ⊢
    exact hpow m' hCdvd
  · have hm1 : m' = 1 := Nat.eq_one_of_dvd_one hm'1
    subst hm1
    have h60 : Nat.card C = 60 := by rw [Nat.card_congr e.toEquiv, hP]
    exact absurd (h60 ▸ (by norm_num : 2 ∣ 60)) hnot2
  · exfalso
    have := Nat.le_of_dvd (by norm_num) hm'1
    omega

end Res8

end CFSG.RankThree.PartTwo.Sec20

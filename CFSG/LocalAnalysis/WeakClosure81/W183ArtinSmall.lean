module

public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinDefs
public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinForms
import CFSG.GH74.GLS.Stage2.Final.ModelArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.GH74.GLS.Stage2.Final.ModelArith

theorem w183art_small_L2 {p q f M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q = 3 ∨ q = 5)
    (hpq : p ≠ q) (hf1 : 1 ≤ f) (hf2 : f ≤ 2) (hq3 : q ^ f ≠ 3) (hM : M = ordA 1 (q ^ f))
    (hT : ArtinTOrder p M) : False := by
  have hcases : (q = 3 ∧ f = 2 ∧ M = 360) ∨ (q = 5 ∧ f = 1 ∧ M = 60) ∨
      (q = 5 ∧ f = 2 ∧ M = 7800) := by
    rcases hq with rfl | rfl
    · interval_cases f
      · exact absurd (by norm_num : 3 ^ 1 = 3) hq3
      · exact Or.inl ⟨rfl, rfl, by rw [hM]; norm_num [ordA]⟩
    · interval_cases f
      · exact Or.inr (Or.inl ⟨rfl, rfl, by rw [hM]; norm_num [ordA]⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl, by rw [hM]; norm_num [ordA]⟩)
  have hMle : M ≤ 7800 := by
    rcases hcases with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> omega
  have hq5 : M = 7800 → q = 5 := by
    intro h7800
    rcases hcases with ⟨h3, _, h360⟩ | ⟨h5, _, h60⟩ | ⟨h5, _, _⟩
    · omega
    · omega
    · exact h5
  rcases hT with ⟨e, hpe, hMe⟩ | hM2 | hM3 | hM4
  ·
    have he : e ≠ 0 := by rintro rfl; norm_num at hpe
    set x := p ^ e with hxdef
    have hx10 : 10 ≤ x := by omega
    have hpodd : Odd p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h hp2
      · exact h
    have hxodd : Odd x := hpodd.pow
    have hg : Nat.gcd 2 (x - 1) = 2 :=
      Nat.gcd_eq_left (Nat.Odd.sub_odd hxodd odd_one).two_dvd
    have hform := w183art_gcd_mul_ordA_one (x := x) (by omega : 1 ≤ x)
    rw [hg] at hform
    have h2M : 2 * M = x * (x ^ 2 - 1) := by rw [hMe, hform]
    have hx2 : 99 ≤ x ^ 2 - 1 := by
      have h : 100 ≤ x ^ 2 := by
        have := Nat.pow_le_pow_left hx10 2
        norm_num at this ⊢
        exact this
      omega
    have hlow : 990 ≤ x * (x ^ 2 - 1) := by
      have := Nat.mul_le_mul hx10 hx2
      norm_num at this ⊢
      exact this
    have hMge : 495 ≤ M := by omega
    have hM7800 : M = 7800 := by
      rcases hcases with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> omega
    have hxeq : x * (x ^ 2 - 1) = 15600 := by omega
    have hx25 : x ≤ 25 := by
      by_contra h
      have hx26 : 26 ≤ x := by omega
      have hx2' : 675 ≤ x ^ 2 - 1 := by
        have h : 676 ≤ x ^ 2 := by
          have := Nat.pow_le_pow_left hx26 2
          norm_num at this ⊢
          exact this
        omega
      have hbig : 17550 ≤ x * (x ^ 2 - 1) := by
        have := Nat.mul_le_mul hx26 hx2'
        norm_num at this ⊢
        exact this
      omega
    have hx25' : x = 25 := by interval_cases x <;> omega
    have hpx : p ^ e = 25 := by rw [hxdef] at hx25'; exact hx25'
    have hpdvd : p ∣ 25 := by
      rw [← hpx]
      exact dvd_pow_self p he
    have hp5dvd : p ∣ 5 := by
      have h25 : (25 : ℕ) = 5 ^ 2 := by norm_num
      rw [h25] at hpdvd
      exact hp.dvd_of_dvd_pow hpdvd
    have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hp5dvd
    exact hpq (hp5.trans (hq5 hM7800).symm)
  ·
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    by_cases hp_eq3 : p = 3
    · have h5616 : M = 5616 := by
        rw [hM2, hp_eq3]; norm_num [ordA, Finset.prod_Icc_succ_top]
      omega
    · have hp5 : 5 ≤ p := by
        have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
        omega
      have hprod : 372000 ≤ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
        have h1 : 125 ≤ p ^ 3 := by
          have := Nat.pow_le_pow_left hp5 3
          norm_num at this ⊢
          exact this
        have h2 : 24 ≤ p ^ 2 - 1 := by
          have h : 25 ≤ p ^ 2 := by
            have := Nat.pow_le_pow_left hp5 2
            norm_num at this ⊢
            exact this
          omega
        have h3 : 124 ≤ p ^ 3 - 1 := by
          have h : 125 ≤ p ^ 3 := by
            have := Nat.pow_le_pow_left hp5 3
            norm_num at this ⊢
            exact this
          omega
        have := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
        norm_num at this ⊢
        exact this
      have hg : Nat.gcd 3 (p - 1) ≤ 3 :=
        Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (p - 1))
      have hform := w183art_gcd_mul_ordA_two (p := p) (by omega : 1 ≤ p)
      have h3M : 372000 ≤ 3 * M := by
        calc 372000 ≤ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := hprod
          _ = Nat.gcd 3 (p - 1) * ordA 2 p := hform.symm
          _ = Nat.gcd 3 (p - 1) * M := by rw [← hM2]
          _ ≤ 3 * M := Nat.mul_le_mul_right M hg
      have : 124000 ≤ M := by omega
      omega
  ·
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    by_cases hp_eq3 : p = 3
    · have h6048 : M = 6048 := by
        rw [hM3, hp_eq3]; norm_num [ordTwistedA, Finset.prod_Icc_succ_top]
      omega
    · have hp5 : 5 ≤ p := by
        have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
        omega
      have hprod : 378000 ≤ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
        have h1 : 125 ≤ p ^ 3 := by
          have := Nat.pow_le_pow_left hp5 3
          norm_num at this ⊢
          exact this
        have h2 : 24 ≤ p ^ 2 - 1 := by
          have h : 25 ≤ p ^ 2 := by
            have := Nat.pow_le_pow_left hp5 2
            norm_num at this ⊢
            exact this
          omega
        have h3 : 126 ≤ p ^ 3 + 1 := by
          have h : 125 ≤ p ^ 3 := by
            have := Nat.pow_le_pow_left hp5 3
            norm_num at this ⊢
            exact this
          omega
        have := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
        norm_num at this ⊢
        exact this
      have hg : Nat.gcd 3 (p + 1) ≤ 3 :=
        Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (p + 1))
      have hform := w183art_gcd_mul_ordTwistedA_two (p := p)
      have h3M : 378000 ≤ 3 * M := by
        calc 378000 ≤ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := hprod
          _ = Nat.gcd 3 (p + 1) * ordTwistedA 2 p := hform.symm
          _ = Nat.gcd 3 (p + 1) * M := by rw [← hM3]
          _ ≤ 3 * M := Nat.mul_le_mul_right M hg
      have : 126000 ≤ M := by omega
      omega
  ·
    have hpodd : Odd p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h hp2
      · exact h
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hform := two_mul_ordBC_two hpodd
    have hprod : 51840 ≤ p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := by
      have h1 : 81 ≤ p ^ 4 := by
        have := Nat.pow_le_pow_left hp3 4
        norm_num at this ⊢
        exact this
      have h2 : 8 ≤ p ^ 2 - 1 := by
        have h : 9 ≤ p ^ 2 := by
          have := Nat.pow_le_pow_left hp3 2
          norm_num at this ⊢
          exact this
        omega
      have h3 : 80 ≤ p ^ 4 - 1 := by
        have h : 81 ≤ p ^ 4 := by
          have := Nat.pow_le_pow_left hp3 4
          norm_num at this ⊢
          exact this
        omega
      have := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
      norm_num at this ⊢
      exact this
    have h2M : 2 * M = p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := by rw [hM4, hform]
    have : 25920 ≤ M := by omega
    omega

end CFSG.LocalAnalysis.WeakClosure81

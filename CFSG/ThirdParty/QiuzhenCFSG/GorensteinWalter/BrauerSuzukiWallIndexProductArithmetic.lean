module

public import Mathlib.Algebra.Ring.Int.Parity

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The index-product arithmetic in the Brauer--Suzuki--Wall argument

This is the divisibility and parity calculation between Bender's character
equation and the final square calculation.  Degrees remain signed integers.
-/

namespace CFSG.GorensteinWalter

/-- Hall coprimality, the evenness of `k`, and Bender's character equation
force the group index to be half the product of the two signed degrees. -/
public theorem brauerSuzukiWall_index_product_of_degree_equation
    (k n : ℕ) (gamma lambda : ℤ)
    (hkEven : Even k)
    (hn : 0 < n)
    (hcop : Nat.Coprime (2 * k) n)
    (_hgammaNe : gamma ≠ 0)
    (_hlambdaNe : lambda ≠ 0)
    (hdegree : 1 + gamma - lambda = 0)
    (hmain :
      2 * (k : ℤ) ^ 2 * gamma * lambda =
        (n : ℤ) * (gamma * lambda + 4 * lambda - gamma)) :
    2 * (n : ℤ) = gamma * lambda := by
  let f : ℤ := gamma * lambda + 4 * lambda - gamma
  have hnInt : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hnNe : (n : ℤ) ≠ 0 := hnInt.ne'
  have hcopN : Nat.Coprime n (2 * k) := hcop.symm
  have hnTwo : Nat.Coprime n 2 :=
    hcopN.of_dvd_right (dvd_mul_right 2 k)
  have hnK : Nat.Coprime n k :=
    hcopN.of_dvd_right (dvd_mul_left k 2)
  have hnCoeffNat : Nat.Coprime n (2 * k ^ 2) :=
    hnTwo.mul_right (hnK.pow_right 2)
  have hnCoeff : IsCoprime (n : ℤ) (2 * (k : ℤ) ^ 2) := by
    simpa using hnCoeffNat.isCoprime
  have hnDvdRaw :
      (n : ℤ) ∣ (2 * (k : ℤ) ^ 2) * (gamma * lambda) := by
    refine ⟨f, ?_⟩
    calc
      (2 * (k : ℤ) ^ 2) * (gamma * lambda) =
          2 * (k : ℤ) ^ 2 * gamma * lambda := by ring
      _ = (n : ℤ) * f := by simpa [f] using hmain
  have hnDvdProduct : (n : ℤ) ∣ gamma * lambda :=
    hnCoeff.dvd_of_dvd_mul_left hnDvdRaw
  obtain ⟨m, hm⟩ := hnDvdProduct
  have hfEq : f = 2 * (k : ℤ) ^ 2 * m := by
    have hcancel :
        (n : ℤ) * (2 * (k : ℤ) ^ 2 * m) = (n : ℤ) * f := by
      calc
        (n : ℤ) * (2 * (k : ℤ) ^ 2 * m) =
            2 * (k : ℤ) ^ 2 * ((n : ℤ) * m) := by ring
        _ = 2 * (k : ℤ) ^ 2 * (gamma * lambda) := by rw [← hm]
        _ = (n : ℤ) * f := by simpa [f, mul_assoc] using hmain
    exact mul_left_cancel₀ hnNe hcancel.symm
  obtain ⟨k0, hk0⟩ := even_iff_exists_two_mul.mp hkEven
  have hfEight : (8 : ℤ) ∣ f := by
    refine ⟨(k0 : ℤ) ^ 2 * m, ?_⟩
    rw [hfEq, hk0]
    push_cast
    ring
  have hgamma : gamma = lambda - 1 := by
    linarith [hdegree]
  have hfLambda : f = lambda * (lambda + 2) + 1 := by
    dsimp [f]
    rw [hgamma]
    ring
  have hcopLambdaF : IsCoprime lambda f := by
    refine ⟨-(lambda + 2), 1, ?_⟩
    rw [hfLambda]
    ring
  have hlambdaDvdNf : lambda ∣ (n : ℤ) * f := by
    refine ⟨2 * (k : ℤ) ^ 2 * gamma, ?_⟩
    calc
      (n : ℤ) * f = 2 * (k : ℤ) ^ 2 * gamma * lambda := by
        simpa [f] using hmain.symm
      _ = lambda * (2 * (k : ℤ) ^ 2 * gamma) := by ring
  have hlambdaDvdN : lambda ∣ (n : ℤ) :=
    hcopLambdaF.dvd_of_dvd_mul_right hlambdaDvdNf
  have hnOdd : Odd n := hnTwo.odd_of_right
  obtain ⟨ell, hlambda⟩ : ∃ ell : ℤ, lambda = 2 * ell + 1 := by
    rcases Int.even_or_odd' lambda with ⟨ell, heven | hodd⟩
    · exfalso
      obtain ⟨q, hq⟩ := hlambdaDvdN
      have hnEvenInt : Even (n : ℤ) := by
        refine ⟨ell * q, ?_⟩
        rw [hq, heven]
        ring
      have hnEven : Even n := by exact_mod_cast hnEvenInt
      exact (Nat.not_even_iff_odd.mpr hnOdd) hnEven
    · exact ⟨ell, hodd⟩
  have hgammaEll : gamma = 2 * ell := by
    rw [hgamma, hlambda]
    ring
  have hfSquare : f = 4 * (ell + 1) ^ 2 := by
    dsimp [f]
    rw [hgammaEll, hlambda]
    ring
  obtain ⟨r, hell⟩ : ∃ r : ℤ, ell = 2 * r + 1 := by
    rcases Int.even_or_odd' ell with ⟨r, heven | hodd⟩
    · exfalso
      obtain ⟨c, hc⟩ := hfEight
      have hsquareEven : (2 : ℤ) ∣ (ell + 1) ^ 2 := by
        refine ⟨c, ?_⟩
        have hfour : (4 : ℤ) * (ell + 1) ^ 2 = 4 * (2 * c) := by
          calc
            (4 : ℤ) * (ell + 1) ^ 2 = f := hfSquare.symm
            _ = 8 * c := hc
            _ = 4 * (2 * c) := by ring
        exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) hfour
      have hsquareOdd : ¬(2 : ℤ) ∣ (ell + 1) ^ 2 := by
        rw [heven]
        have hform : (2 * r + 1) ^ 2 =
            2 * (2 * r ^ 2 + 2 * r) + 1 := by ring
        rw [hform]
        exact Int.two_not_dvd_two_mul_add_one _
      exact hsquareOdd hsquareEven
    · exact ⟨r, hodd⟩
  have hellTwo : IsCoprime ell (2 : ℤ) := by
    refine ⟨1, -r, ?_⟩
    rw [hell]
    ring
  have hellNext : IsCoprime ell (ell + 1) := by
    exact ⟨-1, 1, by ring⟩
  have hellFour : IsCoprime ell (4 : ℤ) := by
    simpa using hellTwo.mul_right hellTwo
  have hellNextSq : IsCoprime ell ((ell + 1) ^ 2) := by
    simpa [pow_two] using hellNext.mul_right hellNext
  have hellF : IsCoprime ell f := by
    rw [hfSquare]
    exact hellFour.mul_right hellNextSq
  have hellDvdNf : ell ∣ (n : ℤ) * f := by
    refine ⟨4 * (k : ℤ) ^ 2 * lambda, ?_⟩
    calc
      (n : ℤ) * f = 2 * (k : ℤ) ^ 2 * gamma * lambda := by
        simpa [f] using hmain.symm
      _ = ell * (4 * (k : ℤ) ^ 2 * lambda) := by
        rw [hgammaEll]
        ring
  have hellDvdN : ell ∣ (n : ℤ) :=
    hellF.dvd_of_dvd_mul_right hellDvdNf
  have hcopLambdaEll : IsCoprime lambda ell := by
    refine ⟨1, -2, ?_⟩
    rw [hlambda]
    ring
  have hproductDvdN : lambda * ell ∣ (n : ℤ) :=
    hcopLambdaEll.mul_dvd hlambdaDvdN hellDvdN
  have hnTwoInt : IsCoprime (n : ℤ) (2 : ℤ) := by
    simpa using hnTwo.isCoprime
  have hnDvdHalfProduct : (n : ℤ) ∣ lambda * ell := by
    apply hnTwoInt.dvd_of_dvd_mul_left
    simpa [hgammaEll, mul_assoc, mul_comm, mul_left_comm] using
      (show (n : ℤ) ∣ gamma * lambda from ⟨m, hm⟩)
  have hproductPos : (0 : ℤ) < gamma * lambda := by
    by_cases hlambdaPos : 0 < lambda
    · have hgammaPos : 0 < gamma := by
        rw [hgamma]
        omega
      exact mul_pos hgammaPos hlambdaPos
    · have hlambdaNeg : lambda < 0 := by omega
      have hgammaNeg : gamma < 0 := by
        rw [hgamma]
        omega
      exact mul_pos_of_neg_of_neg hgammaNeg hlambdaNeg
  have hhalfPos : (0 : ℤ) < lambda * ell := by
    rw [hgammaEll] at hproductPos
    nlinarith only [hproductPos]
  have hhalfEq : lambda * ell = (n : ℤ) :=
    Int.eq_of_associated_of_nonneg
      (associated_of_dvd_dvd hproductDvdN hnDvdHalfProduct)
      hhalfPos.le hnInt.le
  rw [hgammaEll]
  rw [← hhalfEq]
  ring

end CFSG.GorensteinWalter

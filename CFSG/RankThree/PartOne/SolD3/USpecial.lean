module

public import CFSG.RankThree.PartOne.SolD3.SzSpecial
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open scoped Matrix LinearAlgebra.Projectivization

noncomputable section

theorem factorization_two_div_odd {N g : ℕ} (hg : g ∣ N) (hgodd : Odd g) (hN : N ≠ 0) :
    (N / g).factorization 2 = N.factorization 2 := by
  have hg0 : g ≠ 0 := hgodd.pos.ne'
  have hNg : N / g * g = N := Nat.div_mul_cancel hg
  have hNg0 : N / g ≠ 0 := by
    intro h
    rw [h, zero_mul] at hNg
    exact hN hNg.symm
  have h1 : g.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (by simpa [Nat.two_dvd_ne_zero] using hgodd.not_two_dvd_nat)
  conv_rhs => rw [← hNg]
  rw [Nat.factorization_mul hNg0 hg0]
  simp [h1]

theorem sylowSpecial_projectiveSpecialUnitary
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    SylowSpecial (ProjectiveSpecialUnitaryMatrixGroup J) := by
  classical
  let q := 2 ^ f
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  rcases External.huppert_II_10_12 J q hKcard hfixed hJ with
    ⟨_hΩcard, _rho, _a, _hinj, _hnatural, _hUcard,
      ⟨R, _D, _hRle, _hDle, _hN, _hinf, _hsup, _hcyc, hRcard, hcomm, _hcommcard, _hDcard, _hreg,
        _hcoord, _hDcoord, _hDsurj⟩, _htwo, hGcard, _hthree⟩
  have hq2 : 2 ≤ q := by
    dsimp only [q]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 1 ≤ f by omega))
  have hq3 : q ^ 3 = 2 ^ (3 * f) := by
    dsimp only [q]
    rw [← pow_mul, mul_comm]
  have hqeven : Even q := Nat.even_pow.2 ⟨even_two, by omega⟩
  have hq3odd : Odd (q ^ 3 + 1) := by
    have : Even (q ^ 3) := hqeven.pow_of_ne_zero (by norm_num)
    exact this.add_one
  have hq21odd : Odd (q ^ 2 - 1) := by
    have : Even (q ^ 2) := hqeven.pow_of_ne_zero (by norm_num)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) this odd_one
  have hNne : (q ^ 3 + 1) * 2 ^ (3 * f) * (q ^ 2 - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hq3odd.pos.ne' (by positivity)) hq21odd.pos.ne'
  have hgodd : Odd (Nat.gcd 3 (q + 1)) := by
    have h3 : Nat.gcd 3 (q + 1) ∣ 3 := Nat.gcd_dvd_left _ _
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact by decide
  have hgdvd : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * 2 ^ (3 * f) * (q ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have h1 : Nat.gcd 3 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
    refine h1.trans ?_
    obtain ⟨t, ht⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      rw [ht]
      have h : (t + 1) ^ 2 = (t + 1 + 1) * t + 1 := by ring
      simp only [Nat.add_sub_cancel]
      omega
    rw [this]
    exact dvd_mul_right _ _
  have hGfac : (Nat.card G).factorization 2 = 3 * f := by
    have hG' : Nat.card G = ((q ^ 3 + 1) * 2 ^ (3 * f) * (q ^ 2 - 1)) / Nat.gcd 3 (q + 1) := by
      rw [hGcard, hq3]
    rw [hG', factorization_two_div_odd hgdvd hgodd hNne]
    exact factorization_two_odd_mul hq3odd hq21odd
  have hRcard' : Nat.card R = 2 ^ (Nat.card G).factorization 2 := by
    rw [hRcard, hGfac, hq3]
  exact SylowSpecial.of_card R hRcard' hcomm.ge

end

end CFSG.RankThree.PartOne.SolD3

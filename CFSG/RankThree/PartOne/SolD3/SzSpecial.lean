module

public import CFSG.RankThree.PartOne.SolD3.SylowSpecial
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix LinearAlgebra.Projectivization

noncomputable section

theorem factorization_two_odd_mul {e a c : ℕ} (ha : Odd a) (hc : Odd c) :
    (a * 2 ^ e * c).factorization 2 = e := by
  have ha0 : a ≠ 0 := ha.pos.ne'
  have hc0 : c ≠ 0 := hc.pos.ne'
  have h2 : (2 : ℕ) ^ e ≠ 0 := by positivity
  rw [Nat.factorization_mul (mul_ne_zero ha0 h2) hc0, Nat.factorization_mul ha0 h2]
  have h1 : a.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.two_dvd_ne_zero] using ha.not_two_dvd_nat)
  have h3 : c.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.two_dvd_ne_zero] using hc.not_two_dvd_nat)
  simp [h1, h3, Nat.Prime.factorization_pow Nat.prime_two]

theorem sylowSpecial_suzukiMatrixGroup (m : ℕ) (hm : 0 < m) :
    SylowSpecial (SuzukiMatrixGroup m) := by
  classical
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m pi hpi
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  rcases External.huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_hpi_unique, _hpi_formula, hFp, _hF_pow_four, _hF_order_four, _hF_class, hFcard, _hF_typeA,
      _hroot_mul, hFcomm, _hcommutator_coordinates, _htorus_equiv, _htorus_conjugation,
      _hdisjoint, _hfixed_point_free⟩
  rcases External.huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨_hpres, _hrecognition, _hfaithful, _htwo_raw, _hthree, _hOcard_raw, hGcard,
      _hstabilizer_raw⟩
  have hFcard' : Nat.card F = q ^ 2 := by simpa [F, q] using hFcard
  have hF_le_G : F ≤ SuzukiMatrixGroup m := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  let R : Subgroup (SuzukiMatrixGroup m) := F.subgroupOf (SuzukiMatrixGroup m)
  let eR : R ≃* F := Subgroup.subgroupOfEquivOfLe hF_le_G
  have hRcard : Nat.card R = q ^ 2 := (Nat.card_congr eR.toEquiv).trans hFcard'
  have hq : q ^ 2 = 2 ^ (2 * (2 * m + 1)) := by
    dsimp only [q]
    rw [← pow_mul, mul_comm]
  have hqodd : Odd (q ^ 2 + 1) := by
    have : Even (q ^ 2) := by
      rw [hq]
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
    exact this.add_one
  have hq1odd : Odd (q - 1) := by
    have hqe : Even q := Nat.even_pow.2 ⟨even_two, by omega⟩
    have hqpos : 0 < q := by positivity
    exact Nat.Even.sub_odd hqpos hqe odd_one
  have hGfac : (Nat.card (SuzukiMatrixGroup m)).factorization 2 = 2 * (2 * m + 1) := by
    have hG' : Nat.card (SuzukiMatrixGroup m) = (q ^ 2 + 1) * 2 ^ (2 * (2 * m + 1)) * (q - 1) := by
      rw [hGcard, ← hq]
    rw [hG']
    exact factorization_two_odd_mul hqodd hq1odd
  have hRcard' : Nat.card R = 2 ^ (Nat.card (SuzukiMatrixGroup m)).factorization 2 := by
    rw [hRcard, hGfac, hq]
  have hsp : Subgroup.center R ≤ commutator R :=
    center_le_commutator_of_mulEquiv eR.symm (by rw [hFcomm])
  exact SylowSpecial.of_card R hRcard' hsp

end

end CFSG.RankThree.PartOne.SolD3

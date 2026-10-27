module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Cases

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81 (dihedralDeg)
open SevenFour

theorem deltaP_mul_dParam (p : ℕ) : deltaP p * dParam p = dihedralDeg p := by
  unfold deltaP dihedralDeg
  split_ifs <;> ring

private theorem le_rk_of_eps {W : Type} [CommGroup W] [Finite W] {Y L E : Subgroup (MulAut W)}
    {p e c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hodd : c * orbLen p e ≤ rk ↥(commSub ⊤ E))
    (hfull : ∀ A : Subgroup (MulAut W), A ≤ Y → L ≤ A → F6.IsPGL2 (p ^ e) ↥A →
      c * ((p ^ e - 1) / (p - 1)) ≤ rk ↥(commSub ⊤ E)) :
    (p ^ e - 1) * c / (epsL2 Y L (p ^ e) * (p - 1)) ≤ rk ↥(commSub ⊤ E) := by
  classical
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  unfold epsL2
  split_ifs with hε
  · have he : Even e := even_of_isSquare_pow hp hε.1
    have hdvd := two_mul_sub_one_dvd_pow_sub_one (hp.odd_of_ne_two hp2) he
    have hor : orbLen p e = (p ^ e - 1) / (2 * (p - 1)) := by simp [orbLen, he]
    rw [mul_comm (p ^ e - 1) c, Nat.mul_div_assoc c hdvd, ← hor]
    exact hodd
  · have hdvd := sub_one_dvd_pow_sub_one p e
    rw [one_mul, mul_comm (p ^ e - 1) c, Nat.mul_div_assoc c hdvd]
    rw [not_and_or, not_not] at hε
    rcases hε with hsq | ⟨A, hAY, hLA, hA⟩
    · have he : ¬ Even e := fun he => hsq ⟨p ^ (e / 2), by
        rw [← pow_add, ← two_mul, Nat.two_mul_div_two_of_even he]⟩
      have hor : orbLen p e = (p ^ e - 1) / (p - 1) := by simp [orbLen, he]
      rw [← hor]
      exact hodd
    · exact hfull A hAY hLA hA

theorem w4Lem7_4_holds : W4Lem7_4 := by
  intro W _ _ hW Y L p e q hLY hLn hF hp hp2 he hq hq9 hM
  subst hq
  obtain ⟨E₀, hE₀⟩ := exists_isSylowIn hM
  have hinvY : ∃ t ∈ Y, orderOf t = 2 := by
    obtain ⟨t, htL, ht⟩ := exists_involution hM
    exact ⟨t, hLY htL, ht⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    refine le_trans ?_ (rk_commSub_le_rk E₀)
    exact le_rk_of_eps hp hp2 (dParam_mul_orbLen_le_rk hW hM hp2 hE₀)
      (fun A _ hLA hA => dParam_mul_le_rk_of_isPGL2 hW hM hp2 hLA hA hE₀)
  ·
    rintro ⟨E, -, hE, g, -, hinv⟩
    refine le_trans ?_ (rk_commSub_le_rk E)
    rw [mul_assoc, deltaP_mul_dParam]
    exact le_rk_of_eps hp hp2 (dihedralDeg_mul_orbLen_le_rk hW hM hp2 hE hinv)
      (fun A _ hLA hA => dihedralDeg_mul_le_rk_of_isPGL2 hW hM hp2 hLA hA hE hinv)
  ·
    intro t htY ht hind
    by_cases htL : t ∈ L
    · obtain ⟨x, hx, y, hy, z, hz, hcl⟩ := exists_three_conj_closure_eq hM hp2 hq9 htL ht
      refine ⟨x, y, z, hLY hx, hLY hy, hLY hz, ?_⟩
      rw [hcl, sup_eq_left.2 ((zpowers_le (G := MulAut W)).2 htL)]
    · rcases hind with htL' | ⟨A, hAY, hLA, htA, hA⟩
      · exact absurd htL' htL
      obtain ⟨x, hx, y, hy, z, hz, hcl⟩ :=
        exists_three_conj_closure_eq_of_isPGL2 hM hp2 hq9 hLA hA htA htL ht
      exact ⟨x, y, z, hAY hx, hAY hy, hAY hz, hcl⟩
  ·
    intro he1
    by_cases hq25 : p ^ e = 25
    · refine Or.inr ⟨hq25, le_mParam_of_forall (exists_involution hM) ?_⟩
      intro t htL ht
      exact six_le_rkIdx_of_mem hW hM hp2 hq25 htL ht
    · refine Or.inl (le_mParam_of_forall hinvY ?_)
      intro t htY ht
      exact eight_le_rkIdx hW hLY hLn hF hM hp hp2 he1 hq9 hq25 htY ht
  ·
    refine le_mParam_of_forall hinvY ?_
    intro t htY ht
    exact four_le_rkIdx hW hLY hLn hF hM hp hp2 he hq9 htY ht

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

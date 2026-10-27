module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBExcMarkedModel
public import CFSG.LocalAnalysis.StandardType.GGTableBE6MarkedModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem two_not_dvd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : ¬ 2 ∣ 2 ^ n - 1 := by
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) :=
    (mul_pow_sub_one (by omega : n ≠ 0) 2).symm
  rw [h2n]
  exact Nat.two_not_dvd_two_mul_sub_one (Nat.two_pow_pos _)

private theorem prime_ne_two_of_dvd_two_pow_sub_one {n p : ℕ} (hn : 1 ≤ n)
    (hdvd : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  exact two_not_dvd_two_pow_sub_one hn hdvd

theorem exists_marked_factorization_exc
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBExcInnRow p lab ∨ GGL48TBE6Row p lab ∨ GGL48TBExcTwoRow p lab) :
    LargeEvenLabelAll lab fun R _ I F =>
      ∃ f : MulAut R, GGTableBFieldSylowMark p F f ∧ GGTableBMarkedFactorization p I f := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  have hp2 : p ≠ 2 := by
    rcases hrow with hrow | hrow | hrow
    · obtain ⟨-, hdvd⟩ := hrow
      exact prime_ne_two_of_dvd_two_pow_sub_one hn hdvd
    · obtain ⟨-, hdvd⟩ := hrow
      exact prime_ne_two_of_dvd_two_pow_sub_one hn hdvd
    · obtain ⟨-, -, hp3⟩ := hrow
      rw [hp3]
      norm_num
  have htag : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 := by
    rcases hrow with hrow | hrow | hrow
    · obtain ⟨ht, _⟩ := hrow
      rcases ht with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · obtain ⟨ht, _⟩ := hrow
      exact Or.inl ht
    · obtain ⟨ht, _, _⟩ := hrow
      exact ht
  intro Q hQ
  rcases htag with ht | ht | ht | ht <;> subst ht
  · exact recipeChevalley_and
      (P := fun R _ I F => ∃ f : MulAut R,
        GGTableBFieldSylowMark p F f ∧ GGTableBMarkedFactorization p I f)
      (fun K _ _ hK => exists_marked_chev_E6 K hK hp hp2) hQ
  · exact recipeChevalley_and
      (P := fun R _ I F => ∃ f : MulAut R,
        GGTableBFieldSylowMark p F f ∧ GGTableBMarkedFactorization p I f)
      (fun K _ _ hK => exists_marked_chev_E78 (τ := .E7) (Or.inl rfl) hn K hK hp) hQ
  · exact recipeChevalley_and
      (P := fun R _ I F => ∃ f : MulAut R,
        GGTableBFieldSylowMark p F f ∧ GGTableBMarkedFactorization p I f)
      (fun K _ _ hK => exists_marked_chev_E78 (τ := .E8) (Or.inr rfl) hn K hK hp) hQ
  · exact recipeChevalley_and
      (P := fun R _ I F => ∃ f : MulAut R,
        GGTableBFieldSylowMark p F f ∧ GGTableBMarkedFactorization p I f)
      (fun K _ _ hK => exists_marked_chev_F4 hn K hK hp hp2) hQ

end CFSG.StandardType

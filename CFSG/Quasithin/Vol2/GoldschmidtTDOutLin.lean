module

public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs

public section

namespace CFSG.Quasithin.H13.OutTwoNilp

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived
  (linear_unitary_perfect_cover_outer_derived_diagonal_bound)

theorem statedClassicalModel_psl_of_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {n p f : ℕ} (h : StatedClassicalModel H .PSL n p f) : StatedClassicalModel G .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem statedClassicalModel_psu_of_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {n p f : ℕ} (h : StatedClassicalModel H .PSU n p f) : StatedClassicalModel G .PSU n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

variable {S : Type} [Group S] [Finite S] [IsSimpleGroup S]

theorem twoNilpotent_outer_of_psl_two (hnab : ∃ a b : S, a * b ≠ b * a) {p f : ℕ}
    (h : StatedClassicalModel S .PSL 2 p f) : TwoNilpotent (Outer S) := by
  have := isPerfect_of_simple hnab
  have hm := statedClassicalModel_psl_of_equiv (centerQuotientEquiv hnab) h
  obtain ⟨-, -, -, h2⟩ := linear_unitary_perfect_cover_outer_derived_diagonal_bound S .PSL 2 p f 1
    (Or.inl ⟨rfl, rfl⟩) hm
  exact twoNilpotent_of_comm (h2 rfl rfl)

theorem twoNilpotent_outer_of_odd_diagonal (hnab : ∃ a b : S, a * b ≠ b * a)
    {t : StatedLieTag} {n p f : ℕ} {ε : ℤ} (hε : t = .PSL ∧ ε = 1 ∨ t = .PSU ∧ ε = -1)
    (h : StatedClassicalModel S t n p f) (hodd : Odd (Int.gcd n ((p : ℤ) ^ f - ε))) :
    TwoNilpotent (Outer S) := by
  have := isPerfect_of_simple hnab
  have hm : StatedClassicalModel (S ⧸ Subgroup.center S) t n p f := by
    rcases hε with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact statedClassicalModel_psl_of_equiv (centerQuotientEquiv hnab) h
    · exact statedClassicalModel_psu_of_equiv (centerQuotientEquiv hnab) h
  obtain ⟨-, -, ⟨N, hN, -, hNd, hc⟩, -⟩ :=
    linear_unitary_perfect_cover_outer_derived_diagonal_bound S t n p f ε hε hm
  exact TwoNilpotent.of_normal_odd N (Odd.of_dvd_nat hodd hNd) hc

theorem twoNilpotent_outer_of_three (hnab : ∃ a b : S, a * b ≠ b * a)
    {t : StatedLieTag} {p f : ℕ} {ε : ℤ} (hε : t = .PSL ∧ ε = 1 ∨ t = .PSU ∧ ε = -1)
    (h : StatedClassicalModel S t 3 p f) : TwoNilpotent (Outer S) := by
  refine twoNilpotent_outer_of_odd_diagonal hnab hε h ?_
  have hd : Int.gcd (3 : ℕ) ((p : ℤ) ^ f - ε) ∣ 3 := by
    have h3 := Int.gcd_dvd_left (a := ((3 : ℕ) : ℤ)) (b := (p : ℤ) ^ f - ε)
    exact_mod_cast h3
  exact Odd.of_dvd_nat (by decide) hd

theorem twoNilpotent_outer_of_psl_two_one (hnab : ∃ a b : S, a * b ≠ b * a) {n : ℕ}
    (h : StatedClassicalModel S .PSL n 2 1) : TwoNilpotent (Outer S) := by
  refine twoNilpotent_outer_of_odd_diagonal hnab (Or.inl ⟨rfl, rfl⟩) h ?_
  have h1 : ((2 : ℕ) : ℤ) ^ 1 - 1 = 1 := by norm_num
  rw [h1, Int.gcd_one_right]
  exact odd_one

end CFSG.Quasithin.H13.OutTwoNilp

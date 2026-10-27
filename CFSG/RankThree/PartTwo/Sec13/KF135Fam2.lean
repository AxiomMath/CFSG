module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddGL2
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

open CFSG Subgroup
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace FamOdd

theorem not_dvd_card_outer_L3 {S : Type} [Group S] [Finite S] {τ : CFSG.Open.StatedLieTag}
    (hτ : τ = .PSL ∨ τ = .PSU) {r e p : ℕ} (hr : r.Prime) (he1 : 1 ≤ e) (he3 : e ≤ 3)
    (hS : CFSG.Open.StatedClassicalModel S τ 3 r e) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ∣ Nat.card (Outer S) := by
  obtain ⟨hout, -⟩ :=
    CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound hτ le_rfl hr
      he1 hS
  intro hd
  have h1 := hd.trans hout
  have hd3 : CFSG.RankThree.OuterOrder.determinantParameter τ 3 (r ^ e) ∣ 3 := by
    rcases hτ with rfl | rfl <;> exact Nat.gcd_dvd_left _ _
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have := Nat.le_of_dvd (by omega) h
      omega
  · have := Nat.le_of_dvd (by norm_num) (h.trans hd3)
    omega

theorem odd_card_galoisField {r e : ℕ} [Fact r.Prime] (hr : r ≠ 2) (he : 1 ≤ e) :
    Odd (Nat.card (GaloisField r e)) := by
  rw [GaloisField.card r e (by omega)]
  exact ((Fact.out : r.Prime).odd_of_ne_two hr).pow

theorem psl3_hyp_false {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)}
    {x u : MulAut S} {V : Subgroup (MulAut S)} {r e : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (he1 : 1 ≤ e) (he3 : e ≤ 3) (φ : S ≃* projSL 3 (GaloisField r e))
    (h : KF135Hyp S p P x u V) : False := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 r e :=
    ⟨Fact.out, he1, by norm_num, by simp, by simp⟩
  have hS := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ
  have hP := P_le_inner_of_not_dvd h
    (not_dvd_card_outer_L3 (Or.inl rfl) Fact.out he1 he3 hS h.prime h.seven_le)
  refine false_of_noTwoAut h (V_le_inner_of_mem h (hP h.x_mem)) ?_
  exact NoTwoAut.of_mulEquiv φ
    (noTwoAut_of_le_range_toPGL3 (GaloisField r e) (odd_card_galoisField hr he1) h.prime
      (by linarith [h.seven_le]) _ (projSL_le_range_toPGL3 3 _))

theorem psu3_hyp_false {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)}
    {x u : MulAut S} {V : Subgroup (MulAut S)} {r e : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (he1 : 1 ≤ e) (he3 : e ≤ 3) (φ : S ≃* projSU 3 r e) (h : KF135Hyp S p P x u V) : False := by
  have hodd : Odd (r ^ e) := ((Fact.out : r.Prime).odd_of_ne_two hr).pow
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 r e := by
    refine ⟨Fact.out, he1, le_rfl, ?_⟩
    intro h32
    have h2 : r ^ e = 2 := (Prod.mk.inj h32).2
    rw [h2] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) even_two
  have hS := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm φ
  have hP := P_le_inner_of_not_dvd h
    (not_dvd_card_outer_L3 (Or.inr rfl) Fact.out he1 he3 hS h.prime h.seven_le)
  refine false_of_noTwoAut h (V_le_inner_of_mem h (hP h.x_mem)) ?_
  exact NoTwoAut.of_mulEquiv φ
    (noTwoAut_of_le_range_toPGL3 (GaloisField r (2 * e)) (odd_card_galoisField hr (by omega))
      h.prime (by linarith [h.seven_le]) _ (projSU_le_range_toPGL3 r e))

end FamOdd

theorem kF135At_fam2 : KF135At Fam2 := by
  intro S _ _ p P x u V hF h
  obtain ⟨r, e, hr, hr3, he1, he2, hφ | hφ⟩ := hF
  · obtain ⟨φ⟩ := hφ
    exact (FamOdd.psl3_hyp_false (by omega) he1 (by omega) φ h).elim
  · obtain ⟨φ⟩ := hφ
    exact (FamOdd.psu3_hyp_false (by omega) he1 (by omega) φ h).elim

end CFSG.RankThree.PartTwo.Sec13.KF135Proof

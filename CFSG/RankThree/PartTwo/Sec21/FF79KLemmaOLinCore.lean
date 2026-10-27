module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaOLin

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  (autThreePowInner_of_not_three_dvd_outer mulAut_pow_apply_iterate)

theorem three_dvd_card_outer_of_outer_order_three {S : Type} [Group S] {α : MulAut S}
    (hα : α ^ 3 = 1) (hout : ∀ c : S, α ≠ MulAut.conj c) : 3 ∣ Nat.card (Outer S) := by
  by_contra h3
  have hinn := autThreePowInner_of_not_three_dvd_outer h3
  obtain ⟨a, ha⟩ := hinn α 1 (fun x => by
    rw [← mulAut_pow_apply_iterate, pow_one, hα]
    rfl)
  exact hout a (MulEquiv.ext fun x => by rw [ha x, MulAut.conj_apply])

theorem prime_power_le_five {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (h5 : p ^ f ≤ 5) : f ≤ 2 ∧ (p ^ f = 2 ∨ p ^ f = 4 ∨ p ^ f = 5) := by
  have h2 := hp.two_le
  have hf2 : f ≤ 2 := by
    by_contra hf3
    have : 2 ^ 3 ≤ p ^ f :=
      (Nat.pow_le_pow_left h2 3).trans (Nat.pow_le_pow_right hp.pos (by omega))
    omega
  refine ⟨hf2, ?_⟩
  interval_cases f
  · have hp5 : p ≤ 5 := by simpa using h5
    interval_cases p <;> simp_all <;> revert hp <;> decide
  · have hp2 : p ≤ 2 := by
      by_contra hp2
      have : 3 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    obtain rfl : p = 2 := by omega
    simp

theorem three_dvd_of_dvd_two_mul {f g : ℕ} (hf1 : 1 ≤ f) (hf : f ≤ 2) (h : 3 ∣ 2 * f * g) :
    3 ∣ g := by
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · exfalso
    have := Nat.le_of_dvd (by omega) h
    interval_cases f <;> omega
  · exact h

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaOLin

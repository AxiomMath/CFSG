module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartOne

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem exists_inner_of_pow_eq_one_of_not_dvd_card_outer {T : Type*} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (hout : ¬ p ∣ Nat.card (Outer T)) (α : MulAut T) (hα : α ^ p = 1) :
    ∃ b : T, MulAut.conj b = α := by
  set o : Outer T := QuotientGroup.mk α with ho
  have hop : o ^ p = 1 := by rw [ho, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hdvd : orderOf o ∣ p := orderOf_dvd_of_pow_eq_one hop
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · have ho1 : o = 1 := orderOf_eq_one_iff.1 h1
    exact (QuotientGroup.eq_one_iff _).1 ho1
  · exfalso
    apply hout
    rw [← h1]
    exact orderOf_dvd_natCard o

end CFSG.RankThree.PartOne

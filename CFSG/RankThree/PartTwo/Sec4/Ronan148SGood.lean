module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

variable {S : Type} [Group S] [Finite S]

@[expose] def GoodCC425 (s : S) : Prop := ∀ K : Subgroup S, CC425 s K → False

theorem goodCC425_of_card_dvd {s : S} {M B : ℕ}
    (hC : Nat.card (Subgroup.centralizer ({s} : Set S)) ∣ M) (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : typeOrders425 M B = []) : GoodCC425 s := by
  intro K hc
  have hXq := isQuasisimple_theta_quot hc.isQuasisimple
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ M :=
    (card_theta_quot_dvd K).trans ((Subgroup.card_dvd_of_le hc.le_centralizer).trans hC)
  have := card_mem_typeOrders425 hXq hM0 hB hc.isType hdvd
  rw [hfree] at this
  exact List.not_mem_nil this

end CFSG.RankThree.PartTwo.Sec4.Ronan148S

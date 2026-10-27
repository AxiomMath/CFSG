module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4In
public import CFSG.RankThree.PartTwo.Sec21.FF79JL5
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CTypes

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G}

theorem sec35_exists_a_of_JL5 (hJ5 : FF79_JL5) (h : FF79Sec34In b J B A P D) :
    ∃ a ∈ B ⊓ J, orderOf a = 3 ∧ IsLnq 2 2 2 (Lay (J ⊓ Cen a)) := by
  have hJ : IsLnq 5 2 1 J := hJ5 G b J h.hyp
  obtain ⟨-, -, hcard, -, -, -⟩ := e9_types J (B ⊓ J) hJ inf_le_right h.elemB0
  have hne : Nonempty {x : G // x ∈ B ⊓ J ∧ x ≠ 1 ∧ IsLnq 2 2 2 (Lay (J ⊓ Cen x))} := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    rw [Nat.card_of_isEmpty] at hcard
    omega
  obtain ⟨⟨x, hxR, hx1, hxL⟩⟩ := hne
  refine ⟨x, hxR, ?_, hxL⟩
  have h1 := h.elemB0.1
  have hx3 : x ^ 3 = 1 := by
    haveI := h1
    exact elemPow_eq_one_of_isElementaryAbelian x hxR
  exact orderOf_eq_prime hx3 hx1

theorem sec35_exists_a
    (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D) :
    ∃ a ∈ B ⊓ J, orderOf a = 3 ∧ IsLnq 2 2 2 (Lay (J ⊓ Cen a)) :=
  sec35_exists_a_of_JL5 ff79_JL5_holds h

end CFSG.RankThree.PartTwo.Sec21.FF79

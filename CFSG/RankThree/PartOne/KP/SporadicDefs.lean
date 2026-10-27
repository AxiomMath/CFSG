module

public import CFSG.RankThree.PartOne.KP.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def SporadicCoprimeRank (s : TauCeti.SporadicName) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* Carrier s) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card T → ElementaryRankAtMostOne p (MulAut T)

theorem card_outer_eq_of_mulEquiv {T T' : Type*} [Group T] [Group T'] (e : T ≃* T') :
    Nat.card (Outer T) = Nat.card (Outer T') :=
  Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv

theorem sporadicCoprimeRank_of_card_outer_le {s : TauCeti.SporadicName} {k : ℕ} (hk : k < 25)
    (h : Nat.card (Outer (Carrier s)) ≤ k) : SporadicCoprimeRank s := by
  intro T _ _ ⟨e⟩ p hp hp5 hpT
  refine ElementaryRankAtMostOne.of_outer_card_lt hp hpT ?_
  rw [card_outer_eq_of_mulEquiv e]
  have : 25 ≤ p ^ 2 := by nlinarith
  omega

theorem sporadicCoprimeRank_of_not_dvd_outer {s : TauCeti.SporadicName}
    (h : ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card (Outer (Carrier s))) :
    SporadicCoprimeRank s := by
  intro T _ _ ⟨e⟩ p hp hp5 hpT
  refine ElementaryRankAtMostOne.of_not_dvd_outer hp hpT ?_
  rw [card_outer_eq_of_mulEquiv e]
  exact h p hp hp5

end CFSG.RankThree.PartOne

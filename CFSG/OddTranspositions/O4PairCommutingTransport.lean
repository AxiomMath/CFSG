module

public import CFSG.OddTranspositions.O4PairTransport
public import CFSG.GroupTheory.ConjugacyClassCommuting

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GroupTheory

instance : Finite (K25 ≃+* K25) :=
  Finite.of_injective (fun e : K25 ≃+* K25 => (e : K25 → K25))
    (fun a b h => RingEquiv.ext (congrFun h))

instance : Finite PSigmaL225 :=
  Finite.of_equiv (PSL225 × (K25 ≃+* K25)) SemidirectProduct.equivProd.symm

theorem card_comm_class65_eq {u v : PSigmaL225} (hu : u ∈ class65) (hv : v ∈ class65) :
    Nat.card {d : PSigmaL225 // d ∈ class65 ∧ Commute d u} =
      Nat.card {d : PSigmaL225 // d ∈ class65 ∧ Commute d v} :=
  natCard_commuting_conjClass_eq hu hv

theorem card_comm_class65_of_class65t
    (h : Nat.card {d : PSigmaL2t // d ∈ class65t ∧
      Commute d (SemidirectProduct.inr frob25t)} = 11) :
    ∀ u ∈ class65, Nat.card {d : PSigmaL225 // d ∈ class65 ∧ Commute d u} = 11 := by
  intro u hu
  rw [card_comm_class65_eq hu (IsConj.refl _)]
  have htransport := natCard_commuting_mulEquiv psigmaL2Equiv class65t
    (SemidirectProduct.inr frob25t)
  rw [psigmaL2Equiv_image_class65t, psigmaL2Equiv_inr_frob25t] at htransport
  exact htransport.symm.trans h

end CFSG.OddTranspositions.QZ

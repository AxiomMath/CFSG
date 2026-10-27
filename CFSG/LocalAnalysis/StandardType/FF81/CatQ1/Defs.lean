module

public import CFSG.Assembly.InCatalog
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Open.LocalVocabulary

@[expose] public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

def FixedTooBig {K : Type} [Group K] (β : MulAut K) : Prop :=
  27 ∣ Nat.card (fixedSubgroup β) ∨ ¬ 20160 ∣ Nat.card (fixedSubgroup β) ∨
    ∃ x : K, β x = x ∧ orderOf x = 9

def OuterThreeBig (K : Type) [Group K] [Finite K] : Prop :=
  4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) → ∀ β : MulAut K, β ^ 3 = 1 →
    (∀ k : K, β ≠ MulAut.conj k) → FixedTooBig β

def OuterThreeBigAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), P d.1 →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → OuterThreeBig K

theorem OuterThreeBigAt.of_all (h : OuterThreeBigAt (fun _ => True)) :
    ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → OuterThreeBig K :=
  fun K _ _ d e => h K d trivial e

end CFSG.StandardType.FF81.CatQ1

end

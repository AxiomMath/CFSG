module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter3section1

open PFchapter1section1 PFAppendixIII
open PFchapter1section3

/-!
# Basic interfaces for Peterfalvi, Part II, Chapter III, Section 1
-/

/-- Hypothesis (C1). -/
public structure HypothesisC1
    (G : Type*) [Group G] [Finite G] (V : Subgroup G) : Prop where
  V_ne_bot : V ≠ ⊥
  centralizers_two_rank :
    ∀ P : Subgroup G, P ≤ V →
      (∃ p : ℕ, Nat.Prime p ∧ Nat.card P = p) →
        TwoRankAtLeastTwo (Subgroup.centralizer (P : Set G))

end PFchapter3section1
end CFSG.BenderSuzuki




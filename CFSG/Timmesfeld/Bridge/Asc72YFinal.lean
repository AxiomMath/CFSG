module

public import CFSG.Timmesfeld.Bridge.Asc72YU3App
public import CFSG.Timmesfeld.Bridge.Asc72YMain

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.BenderSuzuki

@[expose] def Lemma316L24Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected D →
    Subgroup.center G = ⊥ → (∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K) →
    SmallerHolds (Nat.card G) → ¬ MeetsSq D →
    ∀ u ∈ D, ∀ w ∈ D, ∀ v ∈ D, IsTriangle D u w v → ∀ n : ℕ, Odd n → 1 < n →
      orderOf (u * v * w) = 2 * n → ¬ Reach D u w →
      commutator (localGroup D ((u * v * w) ^ n)) ≠ ⊤ →
      (∀ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)),
        (q : G) = 1 ∨ (q : G) = (u * v * w) ^ n) →
      (∀ S : Sylow 2 G, (D ∩ (S : Set G)).ncard = 3) →
      Nonempty (localGroup D ((u * v * w) ^ n) ⧸ zStar (localGroup D ((u * v * w) ^ n)) ≃*
        PSL2Model 2) →
      False


theorem lemma316Q4Input_of (h : Lemma316L24Input) : Lemma316Q4Input := by
  intro G _ _ D hS hrad hdisc hZ hnorm hIH hnsq u hu w hw v hv htri n hn hn1 hord huw hperf hO2
    hwidth hiso
  rcases hiso with hL | hU
  · exact h G D hS hrad hdisc hZ hnorm hIH hnsq u hu w hw v hv htri n hn hn1 hord huw hperf hO2
      hwidth hL
  · exact false_of_psu3 hS hrad hZ hnsq htri hn hord huw hO2 hU

theorem lemma316Input_of_l24 (h : Lemma316L24Input) : Lemma316Input :=
  lemma316Input_of (lemma316Q4Input_of h)

theorem thirdKindExclusion_of_lemma316L24 (h : Lemma316L24Input) : ThirdKindExclusion :=
  thirdKindExclusion_of_lemma316 (lemma316Input_of_l24 h)

theorem theoremOne_of_lemma316L24 (h : Lemma316L24Input) : TheoremOne :=
  theoremOne_of_lemma316 (lemma316Input_of_l24 h)

end CFSG.Timmesfeld.Bridge.Asc72

namespace CFSG.CGT.Timmesfeld75


theorem lemma215_of_lemma316L24 (h : CFSG.Timmesfeld.Bridge.Asc72.Lemma316L24Input) :
    Lemma215Stmt :=
  lemma215_of_lemma316 (CFSG.Timmesfeld.Bridge.Asc72.lemma316Input_of_l24 h)

end CFSG.CGT.Timmesfeld75

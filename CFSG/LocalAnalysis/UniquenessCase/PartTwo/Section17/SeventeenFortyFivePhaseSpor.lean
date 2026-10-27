module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseBasic
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicMultD1CenterNineOut
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
import CFSG.RankThree.PartOne.CTP.OutEmbed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise commutatorElement

private theorem not_dvd_sporOrd (s : TauCeti.SporadicName) :
    ¬ 31 ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s := by
  cases s <;> decide

section Spor


theorem phase45_false_of_sporadic {X : Type} [Group X] [Finite X] {L A₁ A₂ : Subgroup X}
    (hLn : L.Normal) (hCL : centralizer (L : Set X) = ⊥) {s : TauCeti.SporadicName}
    (e : ↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hA1 : Nat.card A₁ = 31)
    (hA2 : Nat.card A₂ = 31) (hA12 : A₁ ⊓ A₂ = ⊥) (hA12c : A₁ ≤ centralizer (A₂ : Set X)) :
    False := by
  haveI hLnorm : L.Normal := hLn
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hbr : ∀ t : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier t ≃*
        (TauCeti.CFSGIndex.sporadic t).Group) :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hout : Nat.card (Outer ↥L) ∣ 2 := by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.SporadicMultD1.card_outer_sporadic_dvd_two hbr s
  have hquot : Nat.card (X ⧸ L) ≤ 2 :=
    (CFSG.RankThree.PartOne.CTP.card_quotient_le_outer L hCL).trans
      (Nat.le_of_dvd (by norm_num) hout)
  have hndvd : ¬ 31 ∣ Nat.card (X ⧸ L) := by
    intro h
    have h31 : 31 ≤ Nat.card (X ⧸ L) := Nat.le_of_dvd Nat.card_pos h
    omega
  have hA1p : IsPGroup 31 A₁ := IsPGroup.of_card (n := 1) (by rw [hA1, pow_one])
  have hA2p : IsPGroup 31 A₂ := IsPGroup.of_card (n := 1) (by rw [hA2, pow_one])
  have hnorm : A₁ ≤ Subgroup.normalizer (A₂ : Set X) :=
    hA12c.trans (Subgroup.centralizer_le_normalizer (A₂ : Set X))
  have hAp : IsPGroup 31 ↥(A₁ ⊔ A₂) := IsPGroup.to_sup_of_normal_right' hA1p hA2p hnorm
  have hsup : A₁ ⊔ A₂ ≤ L :=
    CFSG.RankThree.PartOne.CTP.le_of_isPGroup_of_not_dvd_card_quotient hAp hndvd
  have hcard : Nat.card (A₁ ⊔ A₂ : Subgroup X) = 31 ^ 2 :=
    (phase45_card_sup hA1 hA2 hA12 hA12c).1
  have hdvd : 31 ^ 2 ∣ Nat.card L := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hsup
  have hLcard : Nat.card L = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (Nat.card_congr e.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s)
  rw [hLcard] at hdvd
  exact not_dvd_sporOrd s hdvd

end Spor

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

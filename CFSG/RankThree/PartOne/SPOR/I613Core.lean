module

public import CFSG.RankThree.PartOne.SPOR.I613Plane
public import CFSG.RankThree.PartOne.Census3.NativeForm
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.S11c.J4Plane
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneHe
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneON
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneTh

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Census3
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped commutatorElement

theorem item613Item6_core
    {X : Type} [Group X] [Finite X] [hs : IsSimpleGroup X] (h6 : ThmThreeItem6 X) {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) {E : Subgroup X} [IsElementaryAbelian p E]
    (hcard : p ^ 2 ≤ Nat.card E) {S : Subgroup X} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hEN : E ≤ Subgroup.normalizer (S : Set X)) (hSE : ⁅S, E⁆ = S) : False := by
  obtain ⟨s, hsmem, ⟨e⟩⟩ := h6
  have : IsSimpleGroup s.Group := e.symm.isSimpleGroup
  obtain ⟨eC⟩ := nonempty_carrier_mulEquiv_of_mem hsmem
  let eXC : X ≃* Carrier s := e.trans eC.symm
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (IsElementaryAbelian.isPGroup p E)
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hk ▸ hcard)
  have hdvd : p ^ 2 ∣ Nat.card (Carrier s) := by
    rw [← Nat.card_congr eXC.toEquiv]
    exact (hk ▸ pow_dvd_pow p hk2 : p ^ 2 ∣ Nat.card E).trans (Subgroup.card_subgroup_dvd_card E)
  have hpair := CTP.sporadicPair_of_sq_dvd hsmem hp (by omega) hdvd
  simp only [CTP.SporadicPair, CTP.SporadicPairNC, CTP.SporadicPairAb] at hpair
  rcases hpair with
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact item613_false_of_planes hp (by omega) (fun hnab E' U hpl =>
      j4LargePrimePlaneCentralization X hs hnab ⟨eXC⟩ _ E' U hpl) hcard hS1 hS2 hEN hSE
  · omega
  · omega
  · omega
  · exact item613_false_of_planes hp (by omega) (fun hnab E' U hpl =>
      sporadicPlanesCentralize_He X hs hnab ⟨eXC⟩ _ E' U hpl) hcard hS1 hS2 hEN hSE
  · omega
  · exact item613_false_of_planes hp (by omega) (fun hnab E' U hpl =>
      sporadicPlanesCentralize_ONan X hs hnab ⟨eXC⟩ _ E' U hpl) hcard hS1 hS2 hEN hSE
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact item613_false_of_planes hp (by omega) (fun hnab E' U hpl =>
      sporadicPlanesCentralize_Th X hs hnab ⟨eXC⟩ _ E' U hpl) hcard hS1 hS2 hEN hSE

end CFSG.RankThree.PartOne.SPOR

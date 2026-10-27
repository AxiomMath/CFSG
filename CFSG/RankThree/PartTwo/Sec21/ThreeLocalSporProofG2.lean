module

public import CFSG.RankThree.PartTwo.Sec21.ThreeLocalSporProofChar
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.RootLocalComponentFree
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.RankThree.PartTwo.Sec6.ThreeLocalSporProof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem centCharThree_adjointGroup_G2 {K : Type} [Field K] [Finite K] [CharP K 3]
    (z : adjointGroup Tag.G2 K) (hz : orderOf z = 3) :
    IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set (adjointGroup Tag.G2 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hP1 : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    have h1 : z = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_zpowers z
    rw [h1, orderOf_one] at hz
    omega
  obtain ⟨hchar, -⟩ := RootWeightDatum.defining_characteristic_root_local_groups_component_free
    (RootWeightDatum.ordinary Tag.G2) 3 (Subgroup.zpowers z) hP hP1
    (Subgroup.centralizer (Subgroup.zpowers z : Set (adjointGroup Tag.G2 K))) (Or.inr rfl)
  have hcent : Subgroup.centralizer (Subgroup.zpowers z : Set (adjointGroup Tag.G2 K)) =
      Subgroup.centralizer {z} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact isCharacteristicP_of_mulEquiv (MulEquiv.subgroupCongr hcent) hchar

theorem exists_mulEquiv_G2 {X : Type} [Group X] (h : ChevalleyExceptionalModel X .G2 3 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 3),
      Nonempty (X ≃* adjointGroup Tag.G2 K) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three le_rfl hK
  have hc : Subgroup.center ↥(adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨K, inferInstance, inferInstance, inferInstance,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)⟩⟩

end CFSG.RankThree.PartTwo.Sec6.ThreeLocalSporProof

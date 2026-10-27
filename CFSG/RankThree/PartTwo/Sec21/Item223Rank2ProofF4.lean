module

public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree

@[expose] def ReeF4NativeThreeRankTwo : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) →
    ∀ F : Subgroup ↥(reeFixedGroup .F4 K reeF4Perm
      fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)),
      CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 9

theorem twistedF4EvenThreeRankTwo_of_native
    (h : ReeF4NativeThreeRankTwo) : TwistedF4EvenThreeRankTwo := by
  intro X _ f hX
  obtain ⟨-, -, -, -, -, hiso⟩ := ReeTag.large_Ree_model_Schreier X 2 f hX
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hX
  have ha : 1 ≤ a := by
    have := hadm.2.2.2.2.2
    omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hH : ReeTag.F4.reeGamma K a = reeFixedGroup .F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) :=
    ReeTag.reeGamma_eq_reeFixedGroup
  refine Item223RankResProof.pRank_quotient_center_le_two_of_mulEquiv E
    (ReeTag.large_Ree_fixed_group_center_trivial a K hK') fun F hF => ?_
  let ι : ↥(ReeTag.F4.reeGamma K a) ≃* ↥(reeFixedGroup .F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))) := MulEquiv.subgroupCongr hH
  have h9 := h a ha K hK' (F.map ι.toMonoidHom) (Sec4.isElemAbelian_map ι.toMonoidHom hF)
  rwa [Subgroup.card_map_of_injective ι.injective] at h9

end CFSG.RankThree.PartTwo.Sec21

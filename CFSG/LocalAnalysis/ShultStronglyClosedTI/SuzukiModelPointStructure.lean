module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureBasic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiModel

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Open
open scoped LinearAlgebra.Projectivization

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiB_semidirect (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((suzukiU a K).subgroupOf (suzukiB a K)).Normal ∧
      ((suzukiU a K).subgroupOf (suzukiB a K)).IsComplement'
        ((suzukiT a K).subgroupOf (suzukiB a K)) := by
  obtain ⟨-, -, hTcard, hTN, hinf, -, -, hBcard⟩ := suzuki_borel_structure hK
  refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer (suzukiU_le_suzukiB a K)).2
    (sup_le Subgroup.le_normalizer hTN), Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suzukiU_le_suzukiB a K)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suzukiT_le_suzukiB a K)).toEquiv,
      (suzuki_unipotent_structure hK).2.1, hTcard, hBcard]
  · rw [Subgroup.disjoint_def]
    intro x hxU hxT
    have hx : (x : suzukiGroup a K) ∈ suzukiU a K ⊓ suzukiT a K :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hxU, Subgroup.mem_subgroupOf.1 hxT⟩
    rw [hinf, Subgroup.mem_bot] at hx
    exact Subtype.ext hx

theorem suzuki_rank_one_point_structure
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiOmegaSub hK) = (2 ^ (2 * a + 1)) ^ 2 + 1 ∧
    MulAction.IsMultiplyPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) 2 ∧
    (∀ x ∈ suzukiOmega a K, ∀ y ∈ suzukiOmega a K, ∀ x' ∈ suzukiOmega a K,
      ∀ y' ∈ suzukiOmega a K, x ≠ y → x' ≠ y' →
        ∃ g : suzukiGroup a K, g • x = x' ∧ g • y = y') ∧
    suzukiLine a K 0 0 ∈ suzukiOmega a K ∧ suzukiInfty K ≠ suzukiLine a K 0 0 ∧
    MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K) = suzukiB a K ∧
    MulAction.stabilizer (suzukiGroup a K)
      (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) = suzukiB a K ∧
    suzukiU a K ≤ suzukiB a K ∧ suzukiT a K ≤ suzukiB a K ∧
    ((suzukiU a K).subgroupOf (suzukiB a K)).Normal ∧
    ((suzukiU a K).subgroupOf (suzukiB a K)).IsComplement'
      ((suzukiT a K).subgroupOf (suzukiB a K)) ∧
    MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K) ⊓
      MulAction.stabilizer (suzukiGroup a K) (suzukiLine a K 0 0) = suzukiT a K ∧
    IsCyclic (suzukiT a K) ∧ Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 ∧
    (∃ P : Sylow 2 (suzukiGroup a K), (P : Subgroup (suzukiGroup a K)) = suzukiU a K) ∧
    Nat.card (suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 ∧
    (∀ x ∈ suzukiOmega a K \ {suzukiInfty K}, ∀ y ∈ suzukiOmega a K \ {suzukiInfty K},
      ∃! g : suzukiU a K, (g : suzukiGroup a K) • x = y) ∧
    fusionStronglyEmbedded (suzukiB a K) ∧
    2 ≤ twoRank (suzukiGroup a K) ∧ twoRank (suzukiGroup a K) = 2 * a + 1 ∧
    {g | g ∈ suzukiB a K ∧ orderOf g = 2} =
      {g | ∃ v : K, v ≠ 0 ∧ suzukiSElt a K 0 v = g} ∧
    {g | g ∈ suzukiB a K ∧ orderOf g = 2}.ncard = 2 ^ (2 * a + 1) - 1 ∧
    {g | g ∈ suzukiB a K ∧ orderOf g = 2} ⊆
      ((Subgroup.center (suzukiU a K)).map (suzukiU a K).subtype : Set (suzukiGroup a K)) ∧
    (orderOf (suzukiWElt a K) = 2 ∧ suzukiWElt a K • suzukiInfty K = suzukiLine a K 0 0 ∧
      suzukiWElt a K • suzukiLine a K 0 0 = suzukiInfty K) ∧
    ∀ w : suzukiGroup a K, w • suzukiInfty K = suzukiLine a K 0 0 →
      w • suzukiLine a K 0 0 = suzukiInfty K →
      orderOf w = 2 ∧ (∀ t ∈ suzukiT a K, w * t * w⁻¹ = t⁻¹ ∧ w⁻¹ * t * w = t⁻¹) ∧
      ∃ C : Subgroup (suzukiGroup a K),
        (C : Set (suzukiGroup a K)) = {t | t ∈ suzukiT a K ∧ w * t * w⁻¹ = t⁻¹} ∧
        IsCyclic C ∧ Nat.card C = 2 ^ (2 * a + 1) - 1 := by
  obtain ⟨-, hpairs, h2tr, -, -⟩ := suzuki_ovoid_double_transitivity hK
  obtain ⟨hB, hBΩ⟩ := suzuki_ovoid_stabilizer hK
  have hTcard := (suzuki_borel_structure hK).2.2.1
  refine ⟨?_, h2tr, hpairs, suzukiLine_mem_suzukiOmega a K 0 0,
    (suzukiLine_ne_suzukiInfty 0 0).symm, hB, hBΩ, suzukiU_le_suzukiB a K,
    suzukiT_le_suzukiB a K, (suzukiB_semidirect hK).1, (suzukiB_semidirect hK).2,
    suzuki_two_point_stabilizer hK, isCyclic_suzukiT, hTcard, exists_sylow_eq_suzukiU hK,
    (suzuki_unipotent_structure hK).2.1, (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1,
    fusionStronglyEmbedded_suzukiB hK, (by omega : 2 ≤ 2 * a + 1).trans
      (le_twoRank_suzukiGroup hK), twoRank_suzukiGroup hK, ?_, ncard_involutions_suzukiB hK, ?_,
    ⟨orderOf_eq_two_of_swap hK (suzukiWElt_smul_suzukiInfty hK)
      (suzukiWElt_smul_suzukiLine_zero hK), suzukiWElt_smul_suzukiInfty hK,
      suzukiWElt_smul_suzukiLine_zero hK⟩, fun w h₁ h₂ => ?_⟩
  · rw [← (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.2, ← Nat.card_coe_set_eq]
    rfl
  · ext g
    exact mem_suzukiB_and_orderOf_eq_two_iff hK
  · rintro g hg
    obtain ⟨v, -, rfl⟩ := (mem_suzukiB_and_orderOf_eq_two_iff hK).1 hg
    exact suzukiSElt_zero_mem_center hK v
  · have hord := orderOf_eq_two_of_swap hK h₁ h₂
    have hinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← sq, ← hord, pow_orderOf_eq_one])
    refine ⟨hord, fun t ht => ⟨conj_eq_inv_of_swap hK h₁ h₂ ht, ?_⟩, suzukiT a K, ?_,
      isCyclic_suzukiT, hTcard⟩
    · have h := conj_eq_inv_of_swap hK h₁ h₂ ht
      rw [hinv] at h ⊢
      exact h
    · ext t
      exact ⟨fun ht => ⟨ht, conj_eq_inv_of_swap hK h₁ h₂ ht⟩, fun ht => ht.1⟩

end CFSG.ShultStronglyClosedTI.SuzukiModel

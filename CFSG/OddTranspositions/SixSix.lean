module

public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.Timmesfeld.Bridge.Asc72WIso

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_l2Wreath_of_not_isSimpleGroup_minimalNormal
    (hC : HypothesisC (G := G) D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {M : Subgroup G} (hM : Asc72.IsMinimalNormal M) (hMns : ¬ IsSimpleGroup M) :
    ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n) := by
  haveI : M.Normal := hM.1
  obtain ⟨W⟩ := nonempty_wreathData hC.setup hrad hM hMns
  have hcent : Subgroup.centralizer (M : Set G) = ⊥ :=
    centralizer_eq_bot_of_minimal hC.setup hrad hM
  obtain ⟨f, hf, Φ, -⟩ := WreathData.exists_mulEquiv_l2Wreath W hC.setup hcent
  exact ⟨f, W.r, hf, ⟨Φ⟩⟩

theorem le_blockKernel_of_ne_bot (hC : HypothesisC (G := G) D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hK : blockKernel hC.alpha ≠ ⊥) {M : Subgroup G} (hM : Asc72.IsMinimalNormal M) :
    M ≤ blockKernel hC.alpha := by
  classical
  by_contra hnot
  haveI : M.Normal := hM.1
  haveI : (blockKernel hC.alpha).Normal := blockKernel_normal hC.alpha
  have hInfNormal : (M ⊓ blockKernel hC.alpha).Normal := inferInstance
  have hInf := hM.2.2 (M ⊓ blockKernel hC.alpha) hInfNormal inf_le_left
  rcases hInf with hbot | htop
  ·
    have hcomm : (⁅M, blockKernel hC.alpha⁆ : Subgroup G) = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro m hm k hk
      have hmK : m * k * m⁻¹ ∈ blockKernel hC.alpha :=
        (blockKernel_normal hC.alpha).conj_mem k hk m
      have hkM : k * m⁻¹ * k⁻¹ ∈ M := hM.1.conj_mem m⁻¹ (M.inv_mem hm) k
      have h1 : (⁅m, k⁆ : G) ∈ blockKernel hC.alpha := by
        rw [commutatorElement_def]
        exact (blockKernel hC.alpha).mul_mem hmK ((blockKernel hC.alpha).inv_mem hk)
      have h2 : (⁅m, k⁆ : G) ∈ M := by
        rw [commutatorElement_def]
        have he : m * k * m⁻¹ * k⁻¹ = m * (k * m⁻¹ * k⁻¹) := by group
        rw [he]
        exact M.mul_mem hm hkM
      rw [← hbot]
      exact ⟨h2, h1⟩
    have hcomm' : (⁅blockKernel hC.alpha, M⁆ : Subgroup G) = ⊥ := by
      rwa [Subgroup.commutator_comm]
    have hcent : blockKernel hC.alpha ≤ Subgroup.centralizer (M : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
    rw [centralizer_eq_bot_of_minimal hC.setup hrad hM] at hcent
    exact hK (le_bot_iff.mp hcent)
  · exact hnot (by rw [← htop]; exact inf_le_right)

end CFSG.OddTranspositions

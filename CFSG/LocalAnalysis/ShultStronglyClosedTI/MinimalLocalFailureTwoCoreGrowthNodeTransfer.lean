module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthTransfer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_index_two_of_split_two_core {H M B : Subgroup G} (S : Sylow 2 G)
    (hSH : (S : Subgroup G) ≤ H) (hMS : M ≤ S) (hHM : H ≤ Subgroup.normalizer (M : Set G))
    (hMB : M ⊔ B = H) (hcyc : IsCyclic (S ⊓ B : Subgroup G)) {u : G} (huS : u ∈ S)
    (hu : orderOf u = 2) (havoid : ∀ g : G, g⁻¹ * u * g ∉ M) :
    ∃ D : Subgroup G, D.Normal ∧ D.index = 2 := by
  let N := M.subgroupOf (S : Subgroup G)
  have hSM : (S : Subgroup G) ≤ Subgroup.normalizer (M : Set G) := hSH.trans hHM
  let : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMS).mpr hSM
  have hBH : B ≤ H := hMB ▸ le_sup_right
  let ρ : (S ⊓ B : Subgroup G) →* (S : Subgroup G) ⧸ N :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion inf_le_left)
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hsH : (s : G) ∈ ((M ⊔ B : Subgroup G) : Set G) := hMB ▸ hSH s.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left M B (hBH.trans hHM)] at hsH
    obtain ⟨m, hm, b, hb, hmb⟩ := Set.mem_mul.mp hsH
    have hbs : b = m⁻¹ * s := by
      rw [← hmb]
      group
    have hbS : b ∈ (S : Subgroup G) := by
      rw [hbs]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hMS hm)) s.2
    refine ⟨⟨b, hbS, hb⟩, ?_⟩
    change (QuotientGroup.mk' N) ⟨b, hbS⟩ = (QuotientGroup.mk' N) s
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    change b⁻¹ * (s : G) ∈ M
    have hconj : b⁻¹ * (s : G) = b⁻¹ * m * b := by
      rw [← hmb]
      group
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff''.mp (hHM (hBH hb)) m).mp hm
  let : IsCyclic ((S : Subgroup G) ⧸ N) := isCyclic_of_surjective ρ hρ
  let x : (S : Subgroup G) := ⟨u, huS⟩
  have hxN : x ∉ N := by
    intro hx
    have hxM : u ∈ M := hx
    apply havoid 1
    simpa only [inv_one, one_mul, mul_one] using hxM
  have hxorder : orderOf x = 2 := (Subgroup.orderOf_coe x).symm.trans hu
  have hxavoid : ∀ (g : G) (hmem : g⁻¹ * (x : G) * g ∈ (S : Subgroup G)),
      (⟨g⁻¹ * (x : G) * g, hmem⟩ : (S : Subgroup G)) ∉ N :=
    fun g _ hx => havoid g hx
  obtain ⟨-, -, -, -, -, -, hD⟩ :=
    TwoCoreGrowth.thompson_cyclic_two_quotient_transfer S N x hxN hxorder hxavoid
  exact hD

end CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode

module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Idx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def s16t3_normIdx {Q : Type*} [Group Q] (Γ : Subgroup Q) : Prop :=
  ∀ M₁ M₂ M₃, M₁ ∈ Subgroup.normalizer (Γ : Set Q) → M₂ ∈ Subgroup.normalizer (Γ : Set Q) →
    M₃ ∈ Subgroup.normalizer (Γ : Set Q) →
    M₁⁻¹ * M₂ ∈ Γ ∨ M₁⁻¹ * M₃ ∈ Γ ∨ M₂⁻¹ * M₃ ∈ Γ

theorem s16t3_normIdx_of_index_le_two {Q : Type*} [Group Q] [Finite Q] {Γ : Subgroup Q}
    (h : (Γ.subgroupOf (Subgroup.normalizer (Γ : Set Q))).index ≤ 2) : s16t3_normIdx Γ := by
  intro M₁ M₂ M₃ hM₁ hM₂ hM₃
  have h' := CFSG.Quasithin.S15223.mem_of_index_le_two h
    (⟨M₁, hM₁⟩ : ↥(Subgroup.normalizer (Γ : Set Q)))
    ⟨M₂, hM₂⟩ ⟨M₃, hM₃⟩
  simpa [Subgroup.mem_subgroupOf] using h'

theorem s16t3_mem_sup_of_map_mem {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    {L K : Subgroup G} (hK : f.ker = K) {x : G} (h : f x ∈ L.map f) : x ∈ L ⊔ K := by
  obtain ⟨l, hl, hlx⟩ := h
  have hk : l⁻¹ * x ∈ K := by
    rw [← hK, MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]
  rw [← mul_inv_cancel_left l x]
  exact Subgroup.mul_mem_sup hl hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

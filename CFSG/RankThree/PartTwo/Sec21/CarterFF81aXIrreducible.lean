module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aInvSubspaces

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.X_irreducible_of_move
    {B B₁ : Subgroup G} {b b₁ b₂ b₃ : G}
    (hB : B = Subgroup.zpowers b ⊔ B₁) (hB₁ : B₁ = Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hE4 : IsElemAb 3 4 B) (hbB : b ∈ B) (hb₁B : b₁ ∈ B) (hb₂B : b₂ ∈ B) (hb₃B : b₃ ∈ B)
    {X : Subgroup (MulAut ↥B)} {τX : MulAut ↥B} (hτXmem : τX ∈ X)
    (hτX2 : τX * τX = 1)
    (hτXb : τX ⟨b, hbB⟩ = ⟨b, hbB⟩)
    (hτX₁ : τX ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹)
    (hτX₂ : τX ⟨b₂, hb₂B⟩ = (⟨b₂, hb₂B⟩)⁻¹)
    (hτX₃ : τX ⟨b₃, hb₃B⟩ = (⟨b₃, hb₃B⟩)⁻¹)
    (hB1irr : ∀ U₁ : Subgroup ↥B, U₁ ≤ B₁.subgroupOf B →
      (∀ σ : MulAut ↥B, σ ∈ X → σ * τX = τX * σ → Subgroup.map σ U₁ = U₁) →
      U₁ = ⊥ ∨ U₁ = B₁.subgroupOf B)
    (hmove : ∃ σ : MulAut ↥B, σ ∈ X ∧
      σ ⟨b, hbB⟩ ∉ Subgroup.zpowers (⟨b, hbB⟩ : ↥B))
    (hB1not : ∃ σ : MulAut ↥B, σ ∈ X ∧
      Subgroup.map σ (B₁.subgroupOf B) ≠ B₁.subgroupOf B)
    {U : Subgroup ↥B} (hU : ∀ σ : MulAut ↥B, σ ∈ X → Subgroup.map σ U = U) :
    U = ⊥ ∨ U = ⊤ := by
  have hUcomm : ∀ σ : MulAut ↥B, σ ∈ X → σ * τX = τX * σ → Subgroup.map σ U = U :=
    fun σ hσX _ => hU σ hσX
  rcases FF81Hyp.CX_tau_invariant_subgroups hB hB₁ hE4 hbB hb₁B hb₂B hb₃B hτXmem hτX2
      hτXb hτX₁ hτX₂ hτX₃ hB1irr le_top hUcomm with hbot | hzp | hB1 | htop
  · exact Or.inl hbot
  ·
    exfalso
    obtain ⟨σ, hσX, hσb⟩ := hmove
    have hmem : σ ⟨b, hbB⟩ ∈ Subgroup.map σ U :=
      Subgroup.mem_map_of_mem (σ : ↥B →* ↥B) (by rw [hzp]; exact Subgroup.mem_zpowers _)
    rw [hU σ hσX, hzp] at hmem
    exact hσb hmem
  ·
    exfalso
    obtain ⟨σ, hσX, hσne⟩ := hB1not
    apply hσne
    rw [← hB1]
    exact hU σ hσX
  · exact Or.inr htop

end CFSG.RankThree.PartTwo.Sec21.FF81

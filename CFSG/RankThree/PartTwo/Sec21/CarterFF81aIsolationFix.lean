module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aIsolationX
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aIsolation

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem tau_eq_of_conj_commute_fix_b
    {B : Subgroup G} {b b₁ b₂ b₃ : G}
    (hbB : b ∈ B) (hb₁B : b₁ ∈ B) (hb₂B : b₂ ∈ B) (hb₃B : b₃ ∈ B)
    (hB : B = Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hE4 : IsElemAb 3 4 B) (hb3 : orderOf b = 3)
    {X : Subgroup (MulAut ↥B)} {τX : MulAut ↥B}
    (hτXmem : τX ∈ X) (hτX2 : τX * τX = 1)
    (hτXb : τX ⟨b, hbB⟩ = ⟨b, hbB⟩)
    (hτX₁ : τX ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹)
    (hτX₂ : τX ⟨b₂, hb₂B⟩ = (⟨b₂, hb₂B⟩)⁻¹)
    (hτX₃ : τX ⟨b₃, hb₃B⟩ = (⟨b₃, hb₃B⟩)⁻¹)
    (hτXfix : ∀ x : ↥B, τX x = x ↔ x ∈ Subgroup.zpowers (⟨b, hbB⟩ : ↥B))
    {σ : MulAut ↥B} (hσX : σ ∈ X)
    (hcomm : (σ * τX * σ⁻¹) * τX = τX * (σ * τX * σ⁻¹))
    (hσb : (σ * τX * σ⁻¹) ⟨b, hbB⟩ = ⟨b, hbB⟩) :
    σ * τX * σ⁻¹ = τX := by
  let bB : ↥B := ⟨b, hbB⟩
  let τ' : MulAut ↥B := σ * τX * σ⁻¹
  have hτ'2 : τ' * τ' = 1 := by
    rw [show τ' * τ' = σ * (τX * τX) * σ⁻¹ by simp [τ', mul_assoc]]
    rw [hτX2]
    simp
  have hfix : ∀ x : ↥B, τ' x = x → x ∈ Subgroup.zpowers bB := by
    intro x hx
    exact fix_tau'_le_of_conj hbB hb3 hτXfix hσb (by simpa [τ'] using hx)
  exact mulAut_eq_tau_of_commute_fix_line (B := B) hbB hb₁B hb₂B hb₃B hB hE4
    hτXb hτX₁ hτX₂ hτX₃ hτX2 hτ'2 hcomm hσb hfix

end CFSG.RankThree.PartTwo.Sec21.FF81

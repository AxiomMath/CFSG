module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces

public section

namespace CFSG.ShultStronglyClosedTI.BorelAlignment

open CFSG.BenderSuzuki MulAction

variable {P Ω : Type*} [Group P] [Finite P] [MulAction P Ω]

theorem sylow_normalizer_eq_stabilizer (S₀ : Sylow 2 P) (p₀ : Ω)
    (hS₀ : Subgroup.normalizer ((S₀ : Subgroup P) : Set P) = stabilizer P p₀)
    (S : Sylow 2 P) :
    ∃ p : Ω, Subgroup.normalizer ((S : Subgroup P) : Set P) = stabilizer P p := by
  obtain ⟨g, rfl⟩ := exists_smul_eq P S₀ S
  refine ⟨g • p₀, ?_⟩
  rw [stabilizer_smul_eq_stabilizer_map_conj, ← hS₀, Subgroup.map_equiv_normalizer_eq]
  rfl

theorem borel_eq_stabilizer (S₀ : Sylow 2 P) (p₀ : Ω)
    (hS₀ : Subgroup.normalizer ((S₀ : Subgroup P) : Set P) = stabilizer P p₀)
    {B : Subgroup P} (hB : IsBorelSubgroup B) : ∃ p : Ω, B = stabilizer P p := by
  obtain ⟨-, S, rfl⟩ := hB
  exact sylow_normalizer_eq_stabilizer S₀ p₀ hS₀ S

theorem borel_pair_alignment (S₀ : Sylow 2 P) (p₀ : Ω)
    (hS₀ : Subgroup.normalizer ((S₀ : Subgroup P) : Set P) = stabilizer P p₀)
    (htwo : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : P, g • a = c ∧ g • b = d)
    {B₁ B₂ : Subgroup P} (hB₁ : IsBorelSubgroup B₁) (hB₂ : IsBorelSubgroup B₂)
    (hne : B₁ ≠ B₂) (a₀ a₁ : Ω) (ha : a₀ ≠ a₁) :
    ∃ g : P, B₁.map (MulAut.conj g).toMonoidHom = stabilizer P a₀ ∧
      B₂.map (MulAut.conj g).toMonoidHom = stabilizer P a₁ := by
  obtain ⟨p₁, rfl⟩ := borel_eq_stabilizer S₀ p₀ hS₀ hB₁
  obtain ⟨p₂, rfl⟩ := borel_eq_stabilizer S₀ p₀ hS₀ hB₂
  have hp : p₁ ≠ p₂ := fun h => hne (by rw [h])
  obtain ⟨g, hg₁, hg₂⟩ := htwo p₁ p₂ a₀ a₁ hp ha
  refine ⟨g, ?_, ?_⟩
  · rw [← stabilizer_smul_eq_stabilizer_map_conj, hg₁]
  · rw [← stabilizer_smul_eq_stabilizer_map_conj, hg₂]

end CFSG.ShultStronglyClosedTI.BorelAlignment

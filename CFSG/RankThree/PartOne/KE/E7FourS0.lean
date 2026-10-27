module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Chevalley.SteinbergBID4WeylCert
public import CFSG.RankThree.PartOne.KE.E7FourLattice

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix

@[expose] def e7F4α : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank e7T12AlphaList

@[expose] def e7F4β : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank e7T12BetaList

@[expose] def e7F4γ : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank e7T12GammaList

theorem e7F4_S0_eq : {α | ∃ l ∈ e7F4S0, α = toVec Tag.E7.rank l} =
    ({e7F4α, -e7F4α} ∪ {e7F4β, -e7F4β} ∪ {e7F4γ, -e7F4γ} : Set (Fin Tag.E7.rank → ℤ)) := by
  ext α
  simp only [e7F4S0, e7T12SigmaList, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, e7F4α, e7F4β, e7F4γ]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inl (Or.inl (Or.inr (by rw [toVec_vneg])))
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr (by rw [toVec_vneg])))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (by rw [toVec_vneg]))
  · rintro (((rfl | rfl) | (rfl | rfl)) | (rfl | rfl))
    · exact ⟨e7T12AlphaList, Or.inl rfl, rfl⟩
    · exact ⟨vneg Tag.E7.rank e7T12AlphaList, Or.inr (Or.inl rfl), by rw [toVec_vneg]⟩
    · exact ⟨e7T12BetaList, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨vneg Tag.E7.rank e7T12BetaList, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
        by rw [toVec_vneg]⟩
    · exact ⟨e7T12GammaList, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
    · exact ⟨vneg Tag.E7.rank e7T12GammaList, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        by rw [toVec_vneg]⟩

theorem e7F4_S0_neg : ∀ α ∈ {α | ∃ l ∈ e7F4S0, α = toVec Tag.E7.rank l},
    -α ∈ {α | ∃ l ∈ e7F4S0, α = toVec Tag.E7.rank l} := by
  intro α hα
  rw [e7F4_S0_eq] at hα ⊢
  rcases hα with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)
  · exact Or.inl (Or.inl (Or.inr rfl))
  · exact Or.inl (Or.inl (Or.inl (neg_neg _)))
  · exact Or.inl (Or.inr (Or.inr rfl))
  · exact Or.inl (Or.inr (Or.inl (neg_neg _)))
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (neg_neg _))

theorem e7F4_S0_isRoot : IsRoot .E7 e7F4α ∧ IsRoot .E7 e7F4β ∧ IsRoot .E7 e7F4γ :=
  ⟨isRoot_toVec (by decide +kernel), isRoot_toVec (by decide +kernel),
    isRoot_toVec (by decide +kernel)⟩

theorem e7F4_S0_fixed : e7F4W *ᵥ e7F4α = e7F4α ∧ e7F4W *ᵥ e7F4β = e7F4β ∧
    e7F4W *ᵥ e7F4γ = e7F4γ := by
  have h : ∀ l ∈ e7F4FList, e7F4W *ᵥ toVec Tag.E7.rank l = toVec Tag.E7.rank l := fun l hl => by
    rw [e7F4W_eq, ← toVec_lmulVec, e7F4W_fixes l hl]
  exact ⟨h _ (by simp [e7F4FList, e7T12AlphaList]), h _ (by simp [e7F4FList, e7T12BetaList]),
    h _ (by simp [e7F4FList, e7T12GammaList])⟩

theorem e7F4_S0_orth : e7F4α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ e7F4β) = 0 ∧
    e7F4α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ e7F4γ) = 0 ∧
    e7F4β ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ e7F4γ) = 0 := by
  unfold e7F4α e7F4β e7F4γ
  decide +kernel

end CFSG.RankThree.PartOne.KE

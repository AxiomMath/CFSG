module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.LocalAnalysis.SignalizerFunctor.HyperplaneGeneration
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.SignalizerFunctorTheorem.Quadratic

theorem IsElemAb.isPGroup {p : ℕ} {G : Type*} [Group G] {A : Subgroup G} (hA : IsElemAb p A) :
    IsPGroup p A :=
  CFSG.Open.IsElemAbelian.isPGroup hA

theorem IsElemAb.mono {p : ℕ} {G : Type*} [Group G] {A B : Subgroup G} (hA : IsElemAb p A)
    (h : B ≤ A) : IsElemAb p B :=
  CFSG.Open.IsElemAbelian.mono hA h

theorem hyperplane_cover {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A Q : Subgroup G} (hA : IsElemAb p A) (hA1 : A ≠ ⊥) (hQ : Nat.Coprime p (Nat.card Q))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    Q ≤ ⨆ (B : Subgroup G) (_ : B ≤ A ∧ Nat.card A = p * Nat.card B),
      Q ⊓ Subgroup.centralizer (B : Set G) := by
  have h := CFSG.SignalizerFunctor.Helpers.elementary_abelian_hyperplane_generation p Fact.out A
    Q hA hA1 hAQ hQ
  refine h.symm.le.trans (iSup_le fun B => iSup_le fun hBA => iSup_le fun hidx => ?_)
  refine le_iSup₂_of_le B ⟨hBA, ?_⟩ le_rfl
  have h1 := (B.subgroupOf A).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv, hidx, mul_comm] at h1
  exact h1.symm

end CFSG.SignalizerFunctorTheorem.Quadratic



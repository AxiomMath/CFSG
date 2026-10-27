module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def CentralizersUniqueInv (M T : Subgroup G) : Prop :=
  ∀ z ∈ T, (∀ t ∈ T, z * t = t * z) → orderOf z = 2 →
    centralizer ({z} : Set G) ≤ M ∧
      ∀ g : G, g ∉ M → ¬ centralizer ({z} : Set G) ≤ M.map (MulAut.conj g).toMonoidHom

theorem CentralizersUnique.inv {M T : Subgroup G} (h : CentralizersUnique M T) :
    CentralizersUniqueInv M T := by
  intro z hz hc ho
  refine h z hz hc ?_
  rintro rfl
  rw [orderOf_one] at ho
  exact absurd ho (by norm_num)

structure WeakClosureSetting (D : Data G) (V₀ V : Subgroup G) : Prop where
  pair : PairFacts D.M V₀ V
  normalizer_eq : normalizer (V : Set G) = D.M
  ti₀ : V₀ ≠ ⊥ → CFSG.CGT.Timmesfeld75.IsTI V₀ ∧ V₀ ≠ V
  normalizer₀ : V₀ ≠ ⊥ → normalizer (V₀ : Set G) = D.M
  gen : V₀ ≠ ⊥ → ∀ v ∈ V, v ∉ V₀ →
    Subgroup.closure {x : G | ∃ m ∈ D.M, x = m * v * m⁻¹} = V
  even : V₀ ≠ ⊥ →
    Even ((D.M ⊓ centralizer (V : Set G)).relIndex (F11.CTilde D.M V₀ V))
  v1 : ∀ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 Q (D.M ⊓ centralizer (V : Set G)) →
    UniqueMax D.M (D.M ⊓ normalizer (Q : Set G))
  hyp14₁ : V₀ ≠ ⊥ → ¬ D.M ⊓ centralizer (V₀ : Set G) ≤ F11.CTilde D.M V₀ V
  hyp14₂ : V₀ ≠ ⊥ → ∀ X : Subgroup G, X ≤ D.M → D.M ⊓ centralizer (V : Set G) ≤ X →
    (X : Set G) * (F11.CTilde D.M V₀ V : Set G) = (D.M : Set G) → UniqueMax D.M X
  central : V₀ ≠ ⊥ → CentralizersUniqueInv D.M D.T

theorem WeakClosureSetting.isElemAbelian {D : Data G} {V₀ V : Subgroup G}
    (h : WeakClosureSetting D V₀ V) : IsElemAbelian 2 V :=
  h.pair.elemAbelian

@[expose] def W3Hyp171 (D : Data G) (H : Subgroup G) : Prop :=
  Fstar H = pCoreOf 2 H ∧ D.T ≤ H ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → 3 < pRank p H →
      ∀ g : G, pRank p ↥(H ⊓ conjSubgroup D.M g) ≤ 1

@[expose] def W3Hyp181 (D : Data G) (H : Subgroup G) : Prop :=
  pRank 3 H ≤ 1 ∧ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M

@[expose] def W3Hyp182 (D : Data G) (H : Subgroup G) : Prop :=
  pRank 3 H ≤ 3 ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → 3 < pRank p H → pRank p ↥(H ⊓ D.M) ≤ 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

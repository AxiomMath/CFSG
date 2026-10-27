module

public import CFSG.RankThree.PartOne.KE.A1Fixed

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open scoped MatrixGroups Pointwise

variable {L : Type} [Field L]

theorem e7_three_a1_sigma_family [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {k : Type} [Field k] [Finite k] [Algebra k L] (hk : Nat.card k = ℓ ^ f)
    (hk4 : 4 ≤ Nat.card k) (n : ModGL Tag.E7 L) (hn : n ∈ monomialSubgroup Tag.E7 L)
    {r₁ r₂ r₃ : Fin Tag.E7.rank → ℤ} (h₁ : IsRoot Tag.E7 r₁) (h₂ : IsRoot Tag.E7 r₂)
    (h₃ : IsRoot Tag.E7 r₃) (hn₁ : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • r₁ = r₁)
    (hn₂ : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • r₂ = r₂)
    (hn₃ : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • r₃ = r₃)
    (o12 : r₁ ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ r₂) = 0)
    (o13 : r₁ ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ r₃) = 0)
    (o23 : r₂ ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ r₃) = 0) :
    ∃ P : (Unit ⊕ Unit) ⊕ Unit → Subgroup (ModGL Tag.E7 L),
      IsSigmaFamily n (iterateFrobenius L ℓ f)
        ({r₁, -r₁} ∪ {r₂, -r₂} ∪ {r₃, -r₃}) P := by
  classical
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 := Or.inr (Or.inr (Or.inl rfl))
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card k := fun c => by
    rw [hk]
    exact iterateFrobenius_def ℓ f c
  have hmw := mapsRootLines_weylQuotientHom (τ := .E7) (R := L) ⟨n, hn⟩
  obtain ⟨s₁, hs₁⟩ := exists_conj_rootSL2_eq hn hmw h₁ hn₁
  obtain ⟨s₂, hs₂⟩ := exists_conj_rootSL2_eq hn hmw h₂ hn₂
  obtain ⟨s₃, hs₃⟩ := exists_conj_rootSL2_eq hn hmw h₃ hn₃
  obtain ⟨P₁, -, hf₁⟩ := a1_fixed_factor (K := k) (iterateFrobenius L ℓ f) hFr hk4 h₁ n s₁ hs₁
  obtain ⟨P₂, -, hf₂⟩ := a1_fixed_factor (K := k) (iterateFrobenius L ℓ f) hFr hk4 h₂ n s₂ hs₂
  obtain ⟨P₃, -, hf₃⟩ := a1_fixed_factor (K := k) (iterateFrobenius L ℓ f) hFr hk4 h₃ n s₃ hs₃
  have hr : ∀ (r : Fin Tag.E7.rank → ℤ), IsRoot Tag.E7 r →
      ∀ α ∈ ({r, -r} : Set (Fin Tag.E7.rank → ℤ)), IsRoot Tag.E7 α := by
    intro r hr' α hα
    rcases hα with rfl | rfl
    exacts [hr', IsRoot.neg hr']
  have hneg : ∀ (r r' : Fin Tag.E7.rank → ℤ),
      r ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ r') = 0 →
        ∀ α ∈ ({r, -r} : Set (Fin Tag.E7.rank → ℤ)), ∀ β ∈ ({r', -r'} : Set (Fin Tag.E7.rank → ℤ)),
          α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
    intro r r' h α hα β hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
      simp [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, h]
  have o12' := hneg _ _ o12
  have o13' := hneg _ _ o13
  have o23' := hneg _ _ o23
  have hS12 : ∀ α ∈ ({r₁, -r₁} ∪ {r₂, -r₂} : Set (Fin Tag.E7.rank → ℤ)), IsRoot Tag.E7 α :=
    fun α hα => hα.elim (hr r₁ h₁ α) (hr r₂ h₂ α)
  have o123 : ∀ α ∈ ({r₁, -r₁} ∪ {r₂, -r₂} : Set (Fin Tag.E7.rank → ℤ)),
      ∀ β ∈ ({r₃, -r₃} : Set (Fin Tag.E7.rank → ℤ)),
        α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 :=
    fun α hα β hβ => hα.elim (fun h => o13' α h β hβ) (fun h => o23' α h β hβ)
  have hU12 := SigmaFactor.union hτ (hr r₁ h₁) (hr r₂ h₂) o12' hf₁ hf₂
  have hU123 := SigmaFactor.union hτ hS12 (hr r₃ h₃) o123 hU12 hf₃
  have hN : torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L
      ({r₁, -r₁} ∪ {r₂, -r₂} ∪ {r₃, -r₃} : Set (Fin Tag.E7.rank → ℤ)) ≤
      (Subgroup.normalizer (rootSpan Tag.E7 L {r₁, -r₁} : Set (ModGL Tag.E7 L)) ⊓
        Subgroup.normalizer (rootSpan Tag.E7 L {r₂, -r₂} : Set (ModGL Tag.E7 L))) ⊓
        Subgroup.normalizer (rootSpan Tag.E7 L {r₃, -r₃} : Set (ModGL Tag.E7 L)) := by
    have hHN : ∀ (r : Fin Tag.E7.rank → ℤ), IsRoot Tag.E7 r → torusGroup Tag.E7 L ≤
        Subgroup.normalizer (rootSpan Tag.E7 L {r, -r} : Set (ModGL Tag.E7 L)) :=
      fun r hr' => torusGroup_le_normalizer_rootSpan (hr r hr')
    have hQN : ∀ (r r' : Fin Tag.E7.rank → ℤ), IsRoot Tag.E7 r → IsRoot Tag.E7 r' →
        r ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ r') = 0 →
        rootSpan Tag.E7 L {r, -r} ≤
          Subgroup.normalizer (rootSpan Tag.E7 L {r', -r'} : Set (ModGL Tag.E7 L)) :=
      fun r r' hr₁ hr₂ h => rootSpan_le_normalizer_of_orth hτ (hr r hr₁) (hr r' hr₂) (hneg r r' h)
    refine sup_le (le_inf (le_inf (hHN r₁ h₁) (hHN r₂ h₂)) (hHN r₃ h₃)) ?_
    rw [rootSpan_union_eq, rootSpan_union_eq]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_inf (le_inf Subgroup.le_normalizer (hQN r₁ r₂ h₁ h₂ o12))
        (hQN r₁ r₃ h₁ h₃ o13)
    · exact le_inf (le_inf (hQN r₂ r₁ h₂ h₁ (by rw [symmetrizedCartan_pair_comm]; exact o12))
        Subgroup.le_normalizer) (hQN r₂ r₃ h₂ h₃ o23)
    · exact le_inf (le_inf (hQN r₃ r₁ h₃ h₁ (by rw [symmetrizedCartan_pair_comm]; exact o13))
        (hQN r₃ r₂ h₃ h₂ (by rw [symmetrizedCartan_pair_comm]; exact o23))) Subgroup.le_normalizer
  exact ⟨Sum.elim (Sum.elim (fun _ => P₁) fun _ => P₂) fun _ => P₃, hU123.toSigma hN⟩

end CFSG.RankThree.PartOne.KE

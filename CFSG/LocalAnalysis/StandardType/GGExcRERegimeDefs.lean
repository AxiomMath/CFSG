module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3
public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList
public import CFSG.LocalAnalysis.StandardType.GGK0CompREMult

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKacExcCentred (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  GGKacExcPair lab p ∧ GGKacCentred lab p

theorem ggKacRE_centred_or_E6Three {lab : LargeEvenLabel} {p : ℕ} (h : GGKacRE lab p) :
    GGKacExcCentred lab p ∨ ((lab.tag = .E6 ∨ lab.tag = .twE6) ∧ p = 3) := by
  by_cases hc : GGKacCentred lab p
  · exact Or.inl ⟨h.toExcPair, hc⟩
  · exact Or.inr (by simpa [GGKacCentred] using hc)

@[expose] def GGKacExcQuasi (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  GGKacExcCentred lab p ∧ ¬ (lab.n = 1 ∧ p = 3)

theorem GGK0Schur.mono {G G' : LargeEvenLabel → ℕ → Prop} (h : GGK0Schur G)
    (hG : ∀ lab p, G' lab p → G lab p) : GGK0Schur G' :=
  fun p lab hlab hg => h p lab hlab (hG lab p hg)

theorem ggKacRE_cases {lab : LargeEvenLabel} {p : ℕ} (h : GGKacRE lab p) :
    GGKacExcQuasi lab p ∨
      (GGKacExcPair lab p ∧ GGKacCentred lab p ∧ lab.n = 1 ∧ p = 3) ∨
      ((lab.tag = .E6 ∨ lab.tag = .twE6) ∧ p = 3) := by
  rcases ggKacRE_centred_or_E6Three h with hc | h3
  · by_cases h13 : lab.n = 1 ∧ p = 3
    · exact Or.inr (Or.inl ⟨hc.1, hc.2, h13.1, h13.2⟩)
    · exact Or.inl ⟨hc, h13⟩
  · exact Or.inr (Or.inr h3)

@[expose] def GGExcCentredRK (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  GGTablePKnownRK fun p n labJ labX => R p n labJ labX ∧ GGKacExcQuasi labX p

@[expose] def GGTypeAExcOneThreeRK : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    GGRegimeTypeA p n labJ labX ∧ GGKacExcPair labX p ∧ GGKacCentred labX p ∧ labX.n = 1 ∧ p = 3

@[expose] def GGTypeAE6ThreeRK : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    GGRegimeTypeA p n labJ labX ∧ (labX.tag = .E6 ∨ labX.tag = .twE6) ∧ p = 3 ∧
      GGKacExcPair labX p

end CFSG.StandardType

end

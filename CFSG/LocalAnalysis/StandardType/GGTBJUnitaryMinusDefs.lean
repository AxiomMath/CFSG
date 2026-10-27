module

public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyStages
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggTBJUniMinusSmallLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
    p ∣ 2 ^ lab.n - 1

@[expose] def ggTBJUniMinusLargeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

theorem ggTBJUniMinusLabel_cases {p : ℕ} {lab : LargeEvenLabel} (h : ggTBJUniMinusLabel p lab) :
    ggTBJUniMinusSmallLabel p lab ∨ ggTBJUniMinusLargeLabel p lab := by
  obtain ⟨htag, hr, hpq⟩ := h
  rcases htag with htag | ⟨htag, hr3⟩
  · by_cases hr5 : 5 ≤ lab.rank
    · exact Or.inr ⟨htag, hr5, hpq⟩
    · exact Or.inl ⟨Or.inl ⟨htag, by omega⟩, hpq⟩
  · exact Or.inl ⟨Or.inr ⟨htag, hr3⟩, hpq⟩

end CFSG.StandardType

namespace CFSG.StandardType.SuSplitRootGen

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n r ε p : ℕ} {K : Type} [Field K]

@[expose] def zeroCoords (S : Finset (Fin r)) : Set (HypIndex r ε) :=
  {a | (∃ i ∈ S, a = .inl i) ∨ (∃ k, a = .inr (.inl k)) ∨ ∃ i ∈ S, a = .inr (.inr i)}

noncomputable abbrev hypFrame {G : Type} [Group G] {h : UnitaryFieldData 2 n K}
    (φ : hypSU h r ε →* G) (τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε) :
    (Fin r → Multiplicative (ZMod p)) →* G :=
  (φ.comp τ).comp (MulEquiv.piMultiplicative fun _ : Fin r => ZMod p).symm.toMonoidHom

end CFSG.StandardType.SuSplitRootGen

end

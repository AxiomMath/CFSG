module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofCensus

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)


section Certs


@[expose] def Census228L3TypeFor (P : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A K K₀ : Subgroup G) (m : ℕ),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    P (X ⧸ aschbacherSolvableCore 3 X) →
    Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A → Nat.card A = 3 ^ 3 →
    A ≤ Subgroup.normalizer (X : Set G) →
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 →
    (∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal) →
    (∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (starOf A X).map (coordGL f) ≤ KFacts.KP14.monomial) →
    (∀ ρ ∈ starOf A X, ¬ IsTransvectionOn ρ) →
    ∀ ρ ∈ starOf A X, IsReflectionOn ρ →
      K ≤ K₀ → K₀ ≤ X → K₀ ≤ Subgroup.centralizer (fixedInG A ρ : Set G) →
      (∀ y ∈ X ⊓ Subgroup.centralizer (fixedInG A ρ : Set G), ∀ k ∈ K₀, y * k * y⁻¹ ∈ K₀) →
      (K = K₀ ∨ StatedClassicalModel K₀ .PSU 3 2 2) →
      Nonempty (K ≃* projSL 2 (GaloisField 2 m)) → 0 < m → Even m →
        List228 (X ⧸ aschbacherSolvableCore 3 X) m

@[expose] def Census228L3TypeLinOdd : Prop :=
  Census228L3TypeFor fun Y _ => ∃ (K : Type) (_ : Field K) (_ : Finite K),
    3 ∣ Nat.card K - 1 ∧ Odd (Nat.card K) ∧
      (Nonempty (Y ≃* projectiveSL 3 K) ∨ Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) K))

@[expose] def Census228L3TypeUniOdd : Prop :=
  Census228L3TypeFor fun Y _ => ∃ (p f : ℕ) (K : Type) (_ : Field K)
    (hK : UnitaryFieldData p f K), 3 ∣ p ^ f + 1 ∧ p ≠ 2 ∧
      (Nonempty (Y ≃* unitaryPSU hK 3) ∨ Nonempty (Y ≃* unitarySU p f K 3))

@[expose] def Census228L3TypeUniTwo : Prop :=
  Census228L3TypeFor fun Y _ => ∃ (f : ℕ) (K : Type) (_ : Field K)
    (hK : UnitaryFieldData 2 f K), 3 ∣ 2 ^ f + 1 ∧
      (Nonempty (Y ≃* unitaryPSU hK 3) ∨ Nonempty (Y ≃* unitarySU 2 f K 3))

@[expose] def Census228L3TypeSLEven : Prop :=
  Census228L3TypeFor fun Y _ => ∃ (K : Type) (_ : Field K) (_ : Finite K),
    3 ∣ Nat.card K - 1 ∧ Even (Nat.card K) ∧
      Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) K)

@[expose] def Census228L3TypePSLEven : Prop :=
  Census228L3TypeFor fun Y _ => ∃ (K : Type) (_ : Field K) (_ : Finite K),
    3 ∣ Nat.card K - 1 ∧ Even (Nat.card K) ∧ Nonempty (Y ≃* projectiveSL 3 K)

theorem census228L3Type_of (hLO : Census228L3TypeLinOdd) (hUO : Census228L3TypeUniOdd)
    (hUT : Census228L3TypeUniTwo) (hSE : Census228L3TypeSLEven)
    (hPE : Census228L3TypePSLEven) : Census228L3Type := by
  intro G _ _ X A K K₀ m hL hT
  rcases hT with ⟨F, _, _, h3, hPSL | hSL⟩ | ⟨p, f, F, _, hF, h3, hPSU | hSU⟩
  · rcases Nat.even_or_odd (Nat.card F) with he | ho
    · exact hPE G X A K K₀ m hL ⟨F, inferInstance, inferInstance, h3, he, hPSL⟩
    · exact hLO G X A K K₀ m hL ⟨F, inferInstance, inferInstance, h3, ho, Or.inl hPSL⟩
  · rcases Nat.even_or_odd (Nat.card F) with he | ho
    · exact hSE G X A K K₀ m hL ⟨F, inferInstance, inferInstance, h3, he, hSL⟩
    · exact hLO G X A K K₀ m hL ⟨F, inferInstance, inferInstance, h3, ho, Or.inr hSL⟩
  · by_cases hp2 : p = 2
    · subst hp2
      exact hUT G X A K K₀ m hL ⟨f, F, inferInstance, hF, h3, Or.inl hPSU⟩
    · exact hUO G X A K K₀ m hL ⟨p, f, F, inferInstance, hF, h3, hp2, Or.inl hPSU⟩
  · by_cases hp2 : p = 2
    · subst hp2
      exact hUT G X A K K₀ m hL ⟨f, F, inferInstance, hF, h3, Or.inr hSU⟩
    · exact hUO G X A K K₀ m hL ⟨p, f, F, inferInstance, hF, h3, hp2, Or.inr hSU⟩

end Certs

end CFSG.RankThree.PartTwo.Sec21

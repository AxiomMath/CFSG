module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res3ProofCensus
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofOuterLin

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def IsL3Type228 (Y : Type) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), 3 ∣ Nat.card K - 1 ∧
      (Nonempty (Y ≃* projectiveSL 3 K) ∨ Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) K))) ∨
  (∃ (p f : ℕ) (K : Type) (_ : Field K) (hK : UnitaryFieldData p f K), 3 ∣ p ^ f + 1 ∧
      (Nonempty (Y ≃* unitaryPSU hK 3) ∨ Nonempty (Y ≃* unitarySU p f K 3)))

@[expose] def Census228L3Type :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A K K₀ : Subgroup G) (m : ℕ),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    IsL3Type228 (X ⧸ aschbacherSolvableCore 3 X) →
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

@[expose] def Census228Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A K K₀ : Subgroup G) (m : ℕ),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    ¬ IsL3Type228 (X ⧸ aschbacherSolvableCore 3 X) →
    Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A → Nat.card A = 3 ^ 3 →
    A ≤ Subgroup.normalizer (X : Set G) →
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 →
    (∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X) →
    (∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (starOf A X).map (coordGL f) ≤ KFacts.KP14.monomial) →
    (∀ ρ ∈ starOf A X, ¬ IsTransvectionOn ρ) →
    ∀ ρ ∈ starOf A X, IsReflectionOn ρ →
      K ≤ K₀ → K₀ ≤ X → K₀ ≤ Subgroup.centralizer (fixedInG A ρ : Set G) →
      (∀ y ∈ X ⊓ Subgroup.centralizer (fixedInG A ρ : Set G), ∀ k ∈ K₀, y * k * y⁻¹ ∈ K₀) →
      (K = K₀ ∨ StatedClassicalModel K₀ .PSU 3 2 2) →
      Nonempty (K ≃* projSL 2 (GaloisField 2 m)) → 0 < m → Even m →
        List228 (X ⧸ aschbacherSolvableCore 3 X) m

namespace Item22Res4Proof

open Item223CensusProof

variable {G : Type} [Group G] [Finite G]


theorem isL3Type228_of_diagonal (hHigh : Outer223High) {X : Subgroup G} {x : G}
    (hL : Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X)) (hx3 : x ^ 3 = 1)
    (hout : Sec4.InducesOuterTheta x X) (hdiag : KFacts.InducesStdKind X x .diagonal) :
    IsL3Type228 (X ⧸ aschbacherSolvableCore 3 X) := by
  obtain ⟨hxN, hxo⟩ := hout
  cases hdiag with
  | psl2 K h => exact (not_inducesKindPSL2_diagonal hx3 h).elim
  | psl n K hn h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    by_cases h3 : 3 ∣ n ∧ 3 ∣ Nat.card K - 1
    · rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
      · exact Or.inl ⟨K, inferInstance, inferInstance, h3.2, Or.inl ⟨e⟩⟩
      · exact ((hHigh _ hL n K hn4 h3.1 h3.2).1.false e).elim
    · exact (hni (isInnerAut_of_mem_linearAutGroup_of_pow_three hn h3 hτ
        (inducedAutHom_pow_eq_one X e hx hx3))).elim
  | sl n K hn h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    by_cases h3 : 3 ∣ n ∧ 3 ∣ Nat.card K - 1
    · rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
      · exact Or.inl ⟨K, inferInstance, inferInstance, h3.2, Or.inr ⟨e⟩⟩
      · exact ((hHigh _ hL n K hn4 h3.1 h3.2).2.false e).elim
    · exact (hni (isInnerAut_of_mem_linearAutGroup_of_pow_three hn h3 hτ
        (by rw [← map_pow, inducedAutHom_pow_eq_one X e hx hx3, map_one]))).elim
  | @psu3 p f K _ hK hq h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    by_cases h3 : 3 ∣ p ^ f + 1
    · exact Or.inr ⟨p, f, K, inferInstance, hK, h3, Or.inl ⟨e⟩⟩
    · obtain ⟨B, hB⟩ := hτ
      rw [← hB] at hni
      exact (hni (isInnerAut_psuConj_of_not_dvd h3 B)).elim
  | @su3 p f K _ hK hq h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    by_cases h3 : 3 ∣ p ^ f + 1
    · exact Or.inr ⟨p, f, K, inferInstance, hK, h3, Or.inr ⟨e⟩⟩
    · obtain ⟨B, hB⟩ := hτ
      rw [← hB] at hni
      exact (hni (isInnerAut_psuConj_of_not_dvd h3 B)).elim
  | psp r K hr h =>
    exact (not_inducesKindPSp_diagonal (by rcases hr with hr | ⟨rfl, -⟩ <;> omega) hx3 h).elim
  | psp4even F h => exact (not_inducesKindPSp4Even_diagonal h).elim
  | g2 K hK3 hK4 h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact (hni hτ).elim
  | sz a K ha hK h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact (hni hτ).elim
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, hx, h⟩ := h
    exact h.elim
  | largeRee a ha K hK h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact (hni hτ).elim

end Item22Res4Proof

open Item22Res4Proof

section Split


theorem inspection228ListMono_of_split (hHigh : Outer223High) (hL3 : Census228L3Type)
    (hInner : Census228Inner) : Inspection228ListMono := by
  intro G _ _ X A K K₀ m hL hAmax hA27 hAN hAC hdiag hmono hnoT ρ hρ hρr hKK hK0X hK0C hnorm hU
    hKm hm0 hme
  by_cases hT : IsL3Type228 (X ⧸ aschbacherSolvableCore 3 X)
  · exact hL3 G X A K K₀ m hL hT hAmax hA27 hAN hAC hdiag hmono hnoT ρ hρ hρr hKK hK0X hK0C hnorm
      hU hKm hm0 hme
  · have hin : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X := fun x hxA hout =>
      hT (isL3Type228_of_diagonal hHigh hL (hAmax.prop.2 x hxA) hout (hdiag x hxA hout))
    exact hInner G X A K K₀ m hL hT hAmax hA27 hAN hAC hin hmono hnoT ρ hρ hρr hKK hK0X hK0C hnorm
      hU hKm hm0 hme

end Split

end CFSG.RankThree.PartTwo.Sec21

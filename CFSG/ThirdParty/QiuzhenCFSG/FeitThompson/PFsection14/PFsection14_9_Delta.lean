module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_8

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.9), Delta and source data
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w
open Section1 Section2 Section3 Section4

public theorem section14_Tmax_source_type_alternative_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (h13 : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section8.typeIIDefinitionData Tmax Q ∨
      Section8.typeIIIDefinitionData Tmax Q ∨
        Section8.typeIVDefinitionData Tmax Q ∨
          Section8.typeVDefinitionData Tmax Q := by
  rcases h13 with
    ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
      hTType, _hCover⟩
  exact hTType

public theorem section14_theorem_14_9_source_typeII_contradiction
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeII : Section8.typeIIDefinitionData Tmax Q)
    (hnotTypeII : ¬ section16TypeII Tmax Q) :
    False := by
  rcases hctx.1 with
    ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice, _hMin, _hFourSixS,
      _hFourSixT⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, hTmax, _hSMF,
      hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
      _hTType, _hCover⟩
  rcases hChoice Tmax Q hTmax hTMF (Or.inr (Or.inl hTypeII)) with
    ⟨Ms, hMs⟩
  exact hnotTypeII
    (Section8.theorem_8_12_bg_typeII_of_source_public hTmax hTMF hMs hTypeII)

@[expose] public def section14_theorem_14_9_bridgeGapData
    {G : Type u} [Group G] [Finite G]
    (Smax W W1 W2 P : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ X Y η01 : Section1.ClassFunction G)
    (p q u : ℕ) : Prop :=
  Section1.supportedOn βS
      (Section13.subgroupSetPreimage Smax
        ((section16NonidentityElements (P : Set G)) ∪
          section16ConjugatesOfSetBySet
            ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (Smax : Set G))) ∧
    Section1.supportedOn βS
      (Section13.subgroupSetPreimage Smax (Section13.typePFAZeroSet Smax W1 W2 P)) ∧
    Section1.IsClassFunction βS ∧
    Section5.cfNormSq βS = ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 2 ∧
    βτ = τS βS ∧
    η01 = η 0 1 ∧
    Γ = βτ - Section1.principalCharacter G + η01 ∧
    (∀ k : ℕ, 0 < k → k < p →
      ∃ (μ0k βSk : Section1.ClassFunction Smax) (βτk : Section1.ClassFunction G),
        Section13.theorem_13_18_hypothesis Smax P W1 μ0k βSk k p ∧
          βτk = τS βSk ∧
          Γ = βτk - Section1.principalCharacter G + η 0 k) ∧
    Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0 ∧
    Γ = Section1.conjugateCharacter Γ ∧
    Theory.Character.IsVirtualCharacter Γ ∧
    Γ = X + Y ∧
    Section13.theorem_13_18_decompositionData p q η X Y

public theorem section14_scalarProduct_finset_sum_left
    {G ι : Type*} [Group G] [Finite G]
    (s : Finset ι) (Φ : ι → Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (s.sum Φ) ψ =
      s.sum fun i => Section1.scalarProduct G (Φ i) ψ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Section1.scalarProduct]
  · intro a s ha ih
    simp [Finset.sum_insert, ha, Section1.scalarProduct_add_left, ih]

public theorem section14_cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (w : ι → ℂ) (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0) :
    Section5.cfNormSq (Section1.weightedFamilySum w χ) =
      ∑ i : ι, Complex.normSq (w i) := by
  classical
  have hself :
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ) =
        ∑ i : ι, star (w i) * w i := by
    calc
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ)
          = ∑ i : ι, star (w i) *
              Section1.scalarProduct G (Section1.weightedFamilySum w χ) (χ i) := by
            simpa using
              Section1.scalarProduct_weightedFamilySum_right
                (Section1.weightedFamilySum w χ) w χ
      _ = ∑ i : ι, star (w i) * w i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i]
  unfold Section5.cfNormSq
  rw [hself, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hnorm : star (w i) * w i = ((Complex.normSq (w i) : ℝ) : ℂ) := by
    simp [Complex.normSq_eq_conj_mul_self]
  rw [hnorm]
  simp

public theorem section14_finite_orthonormal_coeff_normSq_sum_le_cfNormSq
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0)
    (Y : Section1.ClassFunction G) :
    ∑ i : ι, Complex.normSq (Section1.scalarProduct G Y (χ i)) ≤
      Section5.cfNormSq Y := by
  classical
  let w : ι → ℂ := fun i => Section1.scalarProduct G Y (χ i)
  let P : Section1.ClassFunction G := Section1.weightedFamilySum w χ
  let R : Section1.ClassFunction G := Y - P
  have hPχ : ∀ i : ι, Section1.scalarProduct G P (χ i) = w i := by
    intro i
    dsimp [P]
    exact Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i
  have hRχ : ∀ i : ι, Section1.scalarProduct G R (χ i) = 0 := by
    intro i
    dsimp [R]
    rw [Section5.scalarProduct_sub_left, hPχ i]
    dsimp [w]
    simp
  have hRP : Section1.scalarProduct G R P = 0 := by
    dsimp [P]
    rw [Section1.scalarProduct_weightedFamilySum_right]
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [hRχ i]
    simp
  have hPR : Section1.scalarProduct G P R = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRP
  have hdecomp : Y = R + P := by
    dsimp [R, P]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
  have hnorm_decomp :
      Section5.cfNormSq Y = Section5.cfNormSq R + Section5.cfNormSq P := by
    rw [hdecomp]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hRP hPR
  have hPnorm_le : Section5.cfNormSq P ≤ Section5.cfNormSq Y := by
    have hRnonneg : 0 ≤ Section5.cfNormSq R := Section5.cfNormSq_nonneg R
    nlinarith
  have hPnorm :
      Section5.cfNormSq P = ∑ i : ι, Complex.normSq (w i) := by
    dsimp [P]
    exact section14_cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq w χ horth
  simpa [w, hPnorm] using hPnorm_le

public theorem section14_finite_orthonormal_coeff_lower_card_le_cfNormSq
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0)
    (Y : Section1.ClassFunction G)
    (hcoeffLower : ∀ i : ι,
      (1 : ℝ) ≤ Complex.normSq (Section1.scalarProduct G Y (χ i))) :
    (Fintype.card ι : ℝ) ≤ Section5.cfNormSq Y := by
  classical
  have hsum_le :
      (∑ i : ι, Complex.normSq (Section1.scalarProduct G Y (χ i))) ≤
        Section5.cfNormSq Y :=
    section14_finite_orthonormal_coeff_normSq_sum_le_cfNormSq χ horth Y
  have hcard_le_sum :
      (Fintype.card ι : ℝ) ≤
        ∑ i : ι, Complex.normSq (Section1.scalarProduct G Y (χ i)) := by
    calc
      (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
      _ ≤ ∑ i : ι, Complex.normSq (Section1.scalarProduct G Y (χ i)) := by
          exact Finset.sum_le_sum fun i _hi => hcoeffLower i
  exact hcard_le_sum.trans hsum_le

public theorem section14_finset_orthonormal_coeff_lower_card_le_cfNormSq
    {G : Type u} [Group G] [Finite G]
    (E : Finset (Section1.ClassFunction G))
    (hself : ∀ χ ∈ E, Section1.scalarProduct G χ χ = 1)
    (horth : ∀ χ ∈ E, ∀ ψ ∈ E, χ ≠ ψ →
      Section1.scalarProduct G χ ψ = 0)
    (Y : Section1.ClassFunction G)
    (hcoeffLower : ∀ χ ∈ E,
      (1 : ℝ) ≤ Complex.normSq (Section1.scalarProduct G Y χ)) :
    (E.card : ℝ) ≤ Section5.cfNormSq Y := by
  classical
  let χfam : E → Section1.ClassFunction G := fun χ => χ
  have horthFam : ∀ i j : E,
      Section1.scalarProduct G (χfam i) (χfam j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [χfam] using hself i i.2
    · have hvalne : (i : Section1.ClassFunction G) ≠ j := by
        intro hval
        exact hij (Subtype.ext hval)
      simpa [χfam, hij] using horth i i.2 j j.2 hvalne
  have hcoeffFam : ∀ i : E,
      (1 : ℝ) ≤ Complex.normSq (Section1.scalarProduct G Y (χfam i)) := by
    intro i
    exact hcoeffLower i i.2
  simpa [χfam] using
    (section14_finite_orthonormal_coeff_lower_card_le_cfNormSq
      χfam horthFam Y hcoeffFam)

public theorem section14_eta_span_scalarProduct_left_eq_zero
    {G : Type u} [Group G] [Finite G]
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {X χ : Section1.ClassFunction G}
    {p q : ℕ}
    (hXspan : ∃ coeff : ℕ → ℕ → ℂ,
      X = (Finset.range q).sum fun i =>
        (Finset.range p).sum fun k => coeff i k • η i k)
    (hηχ : ∀ i k : ℕ, i < q → k < p →
      Section1.scalarProduct G (η i k) χ = 0) :
    Section1.scalarProduct G X χ = 0 := by
  classical
  rcases hXspan with ⟨coeff, hXeq⟩
  rw [hXeq]
  rw [section14_scalarProduct_finset_sum_left]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [section14_scalarProduct_finset_sum_left]
  refine Finset.sum_eq_zero ?_
  intro k hk
  rw [Section1.scalarProduct_smul_left, hηχ i k (Finset.mem_range.mp hi)
    (Finset.mem_range.mp hk), mul_zero]

public theorem section14_normSq_ge_one_of_intCast_ne_zero_for_oddScalarProduct
    (n : ℤ) (hn : n ≠ 0) :
    (1 : ℝ) ≤ Complex.normSq (n : ℂ) := by
  rw [Complex.normSq_intCast]
  have hnatpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have hnat : 1 ≤ n.natAbs := Nat.succ_le_of_lt hnatpos
  have hsq_nat : (1 : ℕ) ≤ n.natAbs * n.natAbs := by
    nlinarith [hnat]
  have hsq_int_abs : (1 : ℤ) ≤ (n.natAbs * n.natAbs : ℕ) := by
    exact_mod_cast hsq_nat
  have hcast : ((n.natAbs * n.natAbs : ℕ) : ℤ) = n * n := by
    simp
  have hsq_int : (1 : ℤ) ≤ n * n := by
    simpa [hcast] using hsq_int_abs
  exact_mod_cast hsq_int

public theorem section14_normSq_ge_one_of_oddScalarProduct {z : ℂ}
    (hz : Section13.oddScalarProduct z) :
    (1 : ℝ) ≤ Complex.normSq z := by
  rcases hz with ⟨m, hz_eq⟩
  rw [← hz_eq]
  simpa using section14_normSq_ge_one_of_intCast_ne_zero_for_oddScalarProduct
    (2 * m + 1) (by
      intro hzero
      have hodd : Odd (2 * m + 1 : ℤ) := by
        refine ⟨m, ?_⟩
        ring
      rw [hzero] at hodd
      exact Int.not_odd_zero hodd)

@[expose] public def section14_theorem_14_9_late_type_T1ContributionData
    {G : Type u} [Group G] [Finite G]
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (Γ : Section1.ClassFunction G)
    (p q v : ℕ) : Prop :=
  ∃ T1 : Finset (Section1.ClassFunction G),
    ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1.card : ℝ) ∧
      (∀ χ ∈ T1, Section1.scalarProduct G χ χ = 1) ∧
      (∀ χ ∈ T1, ∀ ψ ∈ T1, χ ≠ ψ →
        Section1.scalarProduct G χ ψ = 0) ∧
      (∀ χ ∈ T1, ∀ i k : ℕ, i < q → k < p →
        Section1.scalarProduct G (η i k) χ = 0) ∧
      (∀ χ ∈ T1,
        (1 : ℝ) ≤ Complex.normSq (Section1.scalarProduct G Γ χ))

@[expose] public def section14_theorem_14_9_late_type_T1SourceData
    {G : Type u} [Group G] [Finite G]
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (Γ : Section1.ClassFunction G)
    (p q v : ℕ) : Prop :=
  ∃ T1 : Finset (Section1.ClassFunction G),
    ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1.card : ℝ) ∧
      (∀ χ ∈ T1, Section1.scalarProduct G χ χ = 1) ∧
      (∀ χ ∈ T1, ∀ ψ ∈ T1, χ ≠ ψ →
        Section1.scalarProduct G χ ψ = 0) ∧
      (∀ χ ∈ T1, ∀ i k : ℕ, i < q → k < p →
        Section1.scalarProduct G (η i k) χ = 0) ∧
      (∀ χ ∈ T1,
        Section13.oddScalarProduct (Section1.scalarProduct G Γ χ))

@[expose] public def section14_theorem_14_9_late_type_T1EvenRemainderSourceData
    {G : Type u} [Group G] [Finite G]
    (Γ : Section1.ClassFunction G)
    (T1 : Finset (Section1.ClassFunction G)) : Prop :=
  ∀ χ ∈ T1,
    ∃ m : ℤ, Section1.scalarProduct G Γ χ - 1 = ((2 * m : ℤ) : ℂ)

@[expose] public def section14_theorem_14_9_late_type_T1ParityEquationSourceData
    {G : Type u} [Group G] [Finite G]
    (Γ : Section1.ClassFunction G)
    (T1 : Finset (Section1.ClassFunction G)) : Prop :=
  ∀ χ ∈ T1,
    ∃ m : ℤ, (0 : ℂ) = 1 - Section1.scalarProduct G Γ χ + ((2 * m : ℤ) : ℂ)

@[expose] public def section14_theorem_14_9_late_type_T1DeltaCorrection
    {G : Type u} [Group G] [Finite G]
    (Γ χ Δ : Section1.ClassFunction G) : Prop :=
  (0 : ℂ) = 1 - Section1.scalarProduct G Γ χ + Section1.scalarProduct G Γ Δ ∧
    Theory.Character.IsVirtualCharacter Δ ∧
      Δ = Section1.conjugateCharacter Δ ∧
        Section1.scalarProduct G Δ (Section1.principalCharacter G) = 0

@[expose] public def section14_theorem_14_9_late_type_T1DeltaCorrectionSourceData
    {G : Type u} [Group G] [Finite G]
    (Γ : Section1.ClassFunction G)
    (T1 : Finset (Section1.ClassFunction G)) : Prop :=
  ∀ χ ∈ T1,
    ∃ Δ : Section1.ClassFunction G,
      section14_theorem_14_9_late_type_T1DeltaCorrection Γ χ Δ

@[expose] public def section14_theorem_14_9_late_type_T1DeltaEvenScalarProductSourceData
    {G : Type u} [Group G] [Finite G]
    (Γ : Section1.ClassFunction G)
    (T1 : Finset (Section1.ClassFunction G)) : Prop :=
  ∀ χ ∈ T1, ∀ Δ : Section1.ClassFunction G,
    section14_theorem_14_9_late_type_T1DeltaCorrection Γ χ Δ →
      ∃ m : ℤ, Section1.scalarProduct G Γ Δ = ((2 * m : ℤ) : ℂ)

@[expose] public def section14_theorem_14_9_late_type_T1DeltaParityFactsSourceData
    {G : Type u} [Group G] [Finite G]
    (Γ : Section1.ClassFunction G)
    (T1 : Finset (Section1.ClassFunction G)) : Prop :=
  ∀ χ ∈ T1, ∀ Δ : Section1.ClassFunction G,
    section14_theorem_14_9_late_type_T1DeltaCorrection Γ χ Δ →
      Theory.Character.IsVirtualCharacter Δ ∧
        Δ = Section1.conjugateCharacter Δ ∧
        Section1.scalarProduct G Δ (Section1.principalCharacter G) = 0

public theorem section14_ofConjClassFunction_injective
    {G : Type u} [Group G]
    {φ ψ : Theory.Character.ConjClassFunction G}
    (h : Section1.ofConjClassFunction φ = Section1.ofConjClassFunction ψ) :
    φ = ψ := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  exact congrFun h g

public theorem section14_virtualCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G]
    {φ : Section1.ClassFunction G}
    (hφ : Theory.Character.IsVirtualCharacter φ) :
    Section1.IsClassFunction φ := by
  classical
  rcases hφ with ⟨r, m, n, ρ, rfl⟩
  intro x g
  unfold Theory.Character.virtualCharacterOfRepresentations
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hchar :
      Section1.IsCharacter ((ρ i).character : Section1.ClassFunction G) :=
    ⟨ULift.{u} (Fin (n i) → ℂ), inferInstance, inferInstance, inferInstance,
      Section1.uliftRepresentation (G := G) (V := Fin (n i) → ℂ) (ρ i), by
        ext g
        exact (Section1.uliftRepresentation_character
          (G := G) (V := Fin (n i) → ℂ) (rho := ρ i) g).symm⟩
  rw [Section1.isCharacter_isClassFunction ((ρ i).character) hchar x g]

public theorem section14_scalarProduct_virtual_character_int
    {G : Type u} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G}
    (hφ : Theory.Character.IsVirtualCharacter φ)
    (hψ : Section1.IsCharacter ψ) :
    ∃ z : ℤ, Section1.scalarProduct G φ ψ = (z : ℂ) := by
  classical
  rcases hφ with ⟨r, m, n, ρ, rfl⟩
  have hterm : ∀ i : Fin r,
      ∃ z : ℤ, Section1.scalarProduct G (ρ i).character ψ = (z : ℂ) := by
    intro i
    have hρchar :
        Section1.IsCharacter ((ρ i).character : Section1.ClassFunction G) :=
      ⟨ULift.{u} (Fin (n i) → ℂ), inferInstance, inferInstance, inferInstance,
        Section1.uliftRepresentation (G := G) (V := Fin (n i) → ℂ) (ρ i), by
          ext g
          exact (Section1.uliftRepresentation_character
            (G := G) (V := Fin (n i) → ℂ) (rho := ρ i) g).symm⟩
    rcases Section1.scalarProduct_character_character_eq_nat
        ((ρ i).character : Section1.ClassFunction G) ψ hρchar hψ with
      ⟨k, hk⟩
    exact ⟨(k : ℤ), by simpa using hk⟩
  refine ⟨∑ i : Fin r, m i * Classical.choose (hterm i), ?_⟩
  change Section1.scalarProduct G
      (fun g : G => ∑ i : Fin r,
        (((m i : ℂ) • ((ρ i).character : Section1.ClassFunction G)) g)) ψ =
      ((∑ i : Fin r, m i * Classical.choose (hterm i) : ℤ) : ℂ)
  rw [Section1.scalarProduct_fintype_sum_left]
  simp_rw [Section1.scalarProduct_smul_left]
  calc
    ∑ i : Fin r, (m i : ℂ) *
        Section1.scalarProduct G ((ρ i).character : Section1.ClassFunction G) ψ =
        ∑ i : Fin r, ((m i * Classical.choose (hterm i) : ℤ) : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          let zi : ℤ := Classical.choose (hterm i)
          have hzi :
              Section1.scalarProduct G
                ((ρ i).character : Section1.ClassFunction G) ψ = (zi : ℂ) :=
            Classical.choose_spec (hterm i)
          calc
            (m i : ℂ) *
                Section1.scalarProduct G ((ρ i).character : Section1.ClassFunction G) ψ =
                (m i : ℂ) * (zi : ℂ) := by
                  rw [hzi]
            _ = ((m i * zi : ℤ) : ℂ) := by
                  norm_num
            _ = ((m i * Classical.choose (hterm i) : ℤ) : ℂ) := by
                  rfl
    _ = ((∑ i : Fin r, m i * Classical.choose (hterm i) : ℤ) : ℂ) := by
          simp

public theorem section14_complete_family_member_character
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Fintype ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (i : ι) :
    Section1.IsCharacter (Section1.ofConjClassFunction (χ i)) :=
  (Section1.isBookIrreducibleCharacter_of_representation_irreducible
    (χ i) (hχ.1 i)).1

public theorem section14_scalarProduct_conjugate_left
    {G : Type u} [Finite G]
    (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Section1.conjugateCharacter φ) ψ =
      star (Section1.scalarProduct G φ (Section1.conjugateCharacter ψ)) := by
  simp [Section1.scalarProduct, Section1.conjugateCharacter]

public theorem section14_scalarProduct_real_conjugate_right_eq
    {G : Type u} [Finite G]
    {φ ψ : Section1.ClassFunction G}
    (hφreal : φ = Section1.conjugateCharacter φ)
    (hint : ∃ z : ℤ, Section1.scalarProduct G φ ψ = (z : ℂ)) :
    Section1.scalarProduct G φ (Section1.conjugateCharacter ψ) =
      Section1.scalarProduct G φ ψ := by
  rcases hint with ⟨z, hz⟩
  calc
    Section1.scalarProduct G φ (Section1.conjugateCharacter ψ) =
        star (Section1.scalarProduct G (Section1.conjugateCharacter φ) ψ) := by
          simpa using
            (congrArg star (section14_scalarProduct_conjugate_left φ ψ)).symm
    _ = star (Section1.scalarProduct G φ ψ) := by rw [← hφreal]
    _ = Section1.scalarProduct G φ ψ := by rw [hz]; simp

public theorem section14_complete_family_conjugate_pairing
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (hodd : Odd (Nat.card G)) :
    ∃ i0 : ι, ∃ pair : ι → ι,
      Section1.ofConjClassFunction (χ i0) = Section1.principalCharacter G ∧
        (∀ i,
          Section1.ofConjClassFunction (χ (pair i)) =
            Section1.conjugateCharacter (Section1.ofConjClassFunction (χ i))) ∧
        (∀ i, pair (pair i) = i) ∧
        (∀ i, i ≠ i0 → pair i ≠ i) ∧
        (∀ i, i ≠ i0 → pair i ≠ i0) := by
  classical
  rcases Section3.exists_principal_index_of_completeFamily (G := G)
      (χ := χ) hχ with
    ⟨i0, hi0⟩
  let μ : ι → Section1.ClassFunction G := fun i => Section1.ofConjClassFunction (χ i)
  have hμ_irred : ∀ i, Section1.IsIrreducibleCharacterOnGroup (μ i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 i)
  have hconj_exists : ∀ i : ι,
      ∃ j : ι, μ j = Section1.conjugateCharacter (μ i) := by
    intro i
    rcases Section1.isIrreducibleCharacterOnGroup_conjugateCharacter
        (hμ_irred i) with
      ⟨n, ρ, hρirr, hρchar⟩
    let ψ : Theory.Character.ConjClassFunction G := Theory.Character.characterClassFunction ρ
    have hψirr : Theory.Character.IsIrreducibleConjCharacter ψ := by
      refine ⟨⟨n, ρ, rfl⟩, ?_⟩
      exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
    rcases hχ.2.1 ψ hψirr with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    calc
      μ j = Section1.ofConjClassFunction ψ := by
        dsimp [μ]
        rw [hj]
      _ = ρ.character := Section1.ofConjClassFunction_characterClassFunction ρ
      _ = Section1.conjugateCharacter (μ i) := hρchar.symm
  let pair : ι → ι := fun i => Classical.choose (hconj_exists i)
  have hpair_spec : ∀ i,
      μ (pair i) = Section1.conjugateCharacter (μ i) := by
    intro i
    exact Classical.choose_spec (hconj_exists i)
  have hconj_involutive : ∀ φ : Section1.ClassFunction G,
      Section1.conjugateCharacter (Section1.conjugateCharacter φ) = φ := by
    intro φ
    ext g
    simp [Section1.conjugateCharacter]
  have hpair_pair : ∀ i, pair (pair i) = i := by
    intro i
    apply hχ.2.2
    apply section14_ofConjClassFunction_injective
    dsimp [μ] at hpair_spec
    calc
      Section1.ofConjClassFunction (χ (pair (pair i))) =
          Section1.conjugateCharacter (Section1.ofConjClassFunction (χ (pair i))) :=
            hpair_spec (pair i)
      _ = Section1.conjugateCharacter
            (Section1.conjugateCharacter (Section1.ofConjClassFunction (χ i))) := by
            rw [hpair_spec i]
      _ = Section1.ofConjClassFunction (χ i) := hconj_involutive _
  have hnonprincipal : ∀ i, i ≠ i0 →
      μ i ≠ Section1.principalCharacter G := by
    intro i hi hμi
    apply hi
    apply hχ.2.2
    apply section14_ofConjClassFunction_injective
    dsimp [μ] at hμi hi0
    rw [hμi, hi0]
  have hpair_ne : ∀ i, i ≠ i0 → pair i ≠ i := by
    intro i hi hfix
    rcases hμ_irred i with ⟨n, ρ, hρirr, hρchar⟩
    have hne_principal : ρ.character ≠ Section1.principalCharacter G := by
      intro hρprincipal
      exact hnonprincipal i hi (by rw [hρchar, hρprincipal])
    have hfixed : ρ.character = Section1.conjugateCharacter ρ.character := by
      rw [← hρchar]
      have hs := hpair_spec i
      dsimp [μ] at hs
      rw [hfix] at hs
      exact hs
    exact (Section1.proposition_1_1 hodd ρ hρirr hne_principal) hfixed
  have hpair_ne_i0 : ∀ i, i ≠ i0 → pair i ≠ i0 := by
    intro i hi hpair_i0
    apply hnonprincipal i hi
    have hconj_i :
        Section1.conjugateCharacter (μ i) = Section1.principalCharacter G := by
      dsimp [μ] at hpair_spec hi0
      rw [← hpair_spec i, hpair_i0, hi0]
    calc
      μ i = Section1.conjugateCharacter (Section1.conjugateCharacter (μ i)) := by
        rw [hconj_involutive]
      _ = Section1.conjugateCharacter (Section1.principalCharacter G) := by
        rw [hconj_i]
      _ = Section1.principalCharacter G :=
        Section1.conjugateCharacter_principalCharacter
  exact ⟨i0, pair, hi0, hpair_spec, hpair_pair, hpair_ne, hpair_ne_i0⟩

public theorem section14_even_sum_of_fixedPointFree_pairing
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (pair : ι → ι) (n : ι → ℤ)
    (hpair_mem : ∀ i, i ∈ s → pair i ∈ s)
    (hpair_pair : ∀ i, i ∈ s → pair (pair i) = i)
    (hpair_ne : ∀ i, i ∈ s → pair i ≠ i)
    (hnpair : ∀ i, i ∈ s → n (pair i) = n i) :
    ∃ m : ℤ, (∑ i ∈ s, n i) = 2 * m := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ s : Finset ι, s.card = k →
      (∀ i, i ∈ s → pair i ∈ s) →
      (∀ i, i ∈ s → pair (pair i) = i) →
      (∀ i, i ∈ s → pair i ≠ i) →
      (∀ i, i ∈ s → n (pair i) = n i) →
      ∃ m : ℤ, (∑ i ∈ s, n i) = 2 * m
  have hmain : ∀ k, P k := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih s hcard hmem hinv hne hn
    by_cases hsempty : s = ∅
    · subst hsempty
      refine ⟨0, by simp⟩
    · rcases Finset.nonempty_iff_ne_empty.mpr hsempty with ⟨x, hx⟩
      let y := pair x
      have hy : y ∈ s := hmem x hx
      have hyx : y ≠ x := hne x hx
      let t : Finset ι := (s.erase x).erase y
      have hysx : y ∈ s.erase x := by
        simp [y, hy, hyx]
      have ht_card_lt : t.card < s.card := by
        have ht_sub : t ⊆ s.erase x := by
          intro z hz
          exact (Finset.mem_erase.mp hz).2
        exact lt_of_le_of_lt (Finset.card_le_card ht_sub)
          (Finset.card_erase_lt_of_mem hx)
      have hmem_t : ∀ i, i ∈ t → pair i ∈ t := by
        intro i hi
        have hi_s : i ∈ s :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
        have hpi_s : pair i ∈ s := hmem i hi_s
        have hpi_ne_x : pair i ≠ x := by
          intro hfix
          have hix : i = y := by
            calc
              i = pair (pair i) := (hinv i hi_s).symm
              _ = pair x := by rw [hfix]
              _ = y := rfl
          exact (Finset.mem_erase.mp hi).1 hix
        have hpi_ne_y : pair i ≠ y := by
          intro hfix
          have hpair_y : pair y = x := by
            simpa [y] using hinv x hx
          have hix : i = x := by
            calc
              i = pair (pair i) := (hinv i hi_s).symm
              _ = pair y := by rw [hfix]
              _ = x := hpair_y
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 hix
        simp [t, hpi_s, hpi_ne_x, hpi_ne_y]
      have hinv_t : ∀ i, i ∈ t → pair (pair i) = i := by
        intro i hi
        exact hinv i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
      have hne_t : ∀ i, i ∈ t → pair i ≠ i := by
        intro i hi
        exact hne i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
      have hn_t : ∀ i, i ∈ t → n (pair i) = n i := by
        intro i hi
        exact hn i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
      rcases ih t.card (by simpa [hcard] using ht_card_lt) t rfl
          hmem_t hinv_t hne_t hn_t with
        ⟨m, hm⟩
      have hsum_s :
          (∑ i ∈ s, n i) = n x + n y + ∑ i ∈ t, n i := by
        calc
          (∑ i ∈ s, n i) = ∑ i ∈ insert x (s.erase x), n i := by
            rw [Finset.insert_erase hx]
          _ = n x + ∑ i ∈ s.erase x, n i := by
            rw [Finset.sum_insert (show x ∉ s.erase x by simp)]
          _ = n x + (n y + ∑ i ∈ t, n i) := by
            rw [show (∑ i ∈ s.erase x, n i) =
                ∑ i ∈ insert y t, n i by
              rw [Finset.insert_erase hysx]]
            rw [Finset.sum_insert (show y ∉ t by simp [t])]
          _ = n x + n y + ∑ i ∈ t, n i := by
            ring
      have hny : n y = n x := hn x hx
      refine ⟨n x + m, ?_⟩
      rw [hsum_s, hny, hm]
      ring
  exact hmain s.card s rfl hpair_mem hpair_pair hpair_ne hnpair

public theorem section14_real_virtual_principal_orthogonal_scalarProduct_even_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Γ Δ : Section1.ClassFunction G}
    (hΓvirt : Theory.Character.IsVirtualCharacter Γ)
    (hΓreal : Γ = Section1.conjugateCharacter Γ)
    (hΓone : Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0)
    (hΔvirt : Theory.Character.IsVirtualCharacter Δ)
    (hΔreal : Δ = Section1.conjugateCharacter Δ) :
    ∃ m : ℤ, Section1.scalarProduct G Γ Δ = ((2 * m : ℤ) : ℂ) := by
  classical
  have hoddG : Odd (Nat.card G) := IsMinCE.odd_order
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  rcases section14_complete_family_conjugate_pairing
      (G := G) (χ := χ) hχ hoddG with
    ⟨i0, pair, hi0, hpair_spec, hpair_pair, hpair_ne, hpair_ne_i0⟩
  let μ : ι → Section1.ClassFunction G :=
    fun i => Section1.ofConjClassFunction (χ i)
  have hΓclass : Section1.IsClassFunction Γ :=
    section14_virtualCharacter_isClassFunction hΓvirt
  have hΔclass : Section1.IsClassFunction Δ :=
    section14_virtualCharacter_isClassFunction hΔvirt
  have hΓint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G Γ (μ i) = (z : ℂ) := by
    intro i
    exact section14_scalarProduct_virtual_character_int hΓvirt
      (section14_complete_family_member_character hχ i)
  have hΔint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G Δ (μ i) = (z : ℂ) := by
    intro i
    exact section14_scalarProduct_virtual_character_int hΔvirt
      (section14_complete_family_member_character hχ i)
  let a : Section1.CoeffVector ι := Section3.irreducibleBasisCoeff Γ hΓint
  let d : Section1.CoeffVector ι := Section3.irreducibleBasisCoeff Δ hΔint
  have hΓeval :
      Section1.evalCoeff μ a = Γ := by
    exact Section3.irreducibleBasis_evalCoeff_coeff hχ b hb Γ hΓclass hΓint
  have hΔeval :
      Section1.evalCoeff μ d = Δ := by
    exact Section3.irreducibleBasis_evalCoeff_coeff hχ b hb Δ hΔclass hΔint
  have hΓcoeff_pair : ∀ i : ι, a (pair i) = a i := by
    intro i
    have hcoeffC : (a (pair i) : ℂ) = (a i : ℂ) := by
      calc
        (a (pair i) : ℂ) =
            Section1.scalarProduct G Γ (μ (pair i)) := by
              exact (Section3.irreducibleBasisCoeff_spec Γ hΓint (pair i)).symm
        _ = Section1.scalarProduct G Γ
            (Section1.conjugateCharacter (μ i)) := by
              simpa [μ] using
                congrArg (fun θ => Section1.scalarProduct G Γ θ) (hpair_spec i)
        _ = Section1.scalarProduct G Γ (μ i) :=
            section14_scalarProduct_real_conjugate_right_eq hΓreal (hΓint i)
        _ = (a i : ℂ) :=
            Section3.irreducibleBasisCoeff_spec Γ hΓint i
    exact_mod_cast hcoeffC
  have hΔcoeff_pair : ∀ i : ι, d (pair i) = d i := by
    intro i
    have hcoeffC : (d (pair i) : ℂ) = (d i : ℂ) := by
      calc
        (d (pair i) : ℂ) =
            Section1.scalarProduct G Δ (μ (pair i)) := by
              exact (Section3.irreducibleBasisCoeff_spec Δ hΔint (pair i)).symm
        _ = Section1.scalarProduct G Δ
            (Section1.conjugateCharacter (μ i)) := by
              simpa [μ] using
                congrArg (fun θ => Section1.scalarProduct G Δ θ) (hpair_spec i)
        _ = Section1.scalarProduct G Δ (μ i) :=
            section14_scalarProduct_real_conjugate_right_eq hΔreal (hΔint i)
        _ = (d i : ℂ) :=
            Section3.irreducibleBasisCoeff_spec Δ hΔint i
    exact_mod_cast hcoeffC
  have hΓprincipal_coeff : a i0 = 0 := by
    have hcoeffC : (a i0 : ℂ) = 0 := by
      calc
        (a i0 : ℂ) = Section1.scalarProduct G Γ (μ i0) := by
          exact (Section3.irreducibleBasisCoeff_spec Γ hΓint i0).symm
        _ = Section1.scalarProduct G Γ (Section1.principalCharacter G) := by
          simpa [μ] using
            congrArg (fun θ => Section1.scalarProduct G Γ θ) hi0
        _ = 0 := hΓone
    exact_mod_cast hcoeffC
  let s : Finset ι := Finset.univ.erase i0
  have hpair_mem_s : ∀ i, i ∈ s → pair i ∈ s := by
    intro i hi
    have hi_ne : i ≠ i0 := (Finset.mem_erase.mp hi).1
    exact Finset.mem_erase.mpr ⟨hpair_ne_i0 i hi_ne, Finset.mem_univ _⟩
  have hpair_pair_s : ∀ i, i ∈ s → pair (pair i) = i := by
    intro i _hi
    exact hpair_pair i
  have hpair_ne_s : ∀ i, i ∈ s → pair i ≠ i := by
    intro i hi
    exact hpair_ne i (Finset.mem_erase.mp hi).1
  have hprod_pair : ∀ i, i ∈ s → a (pair i) * d (pair i) = a i * d i := by
    intro i _hi
    rw [hΓcoeff_pair i, hΔcoeff_pair i]
  rcases section14_even_sum_of_fixedPointFree_pairing s pair
      (fun i => a i * d i) hpair_mem_s hpair_pair_s hpair_ne_s
      hprod_pair with
    ⟨m, hm⟩
  have hdot_s : Section1.coeffDot a d = ∑ i ∈ s, a i * d i := by
    unfold Section1.coeffDot
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun i => a i * d i) (Finset.mem_univ i0)
    calc
      (∑ i : ι, a i * d i) =
          (Finset.univ.erase i0).sum (fun i => a i * d i) + a i0 * d i0 := by
            exact hsplit.symm
      _ = (Finset.univ.erase i0).sum (fun i => a i * d i) := by
            rw [hΓprincipal_coeff]
            ring
      _ = ∑ i ∈ s, a i * d i := by
            simp [s]
  have hscalar :
      Section1.scalarProduct G Γ Δ = (Section1.coeffDot a d : ℂ) := by
    rw [← hΓeval, ← hΔeval]
    exact Section3.irreducibleBasis_scalarProduct_evalCoeff hχ a d
  refine ⟨m, ?_⟩
  rw [hscalar, hdot_s, hm]

public theorem section14_theorem_14_9_late_type_T1DeltaEvenScalarProductSourceData_of_parityFacts
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Γ : Section1.ClassFunction G}
    {T1 : Finset (Section1.ClassFunction G)}
    (hΓvirt : Theory.Character.IsVirtualCharacter Γ)
    (hΓreal : Γ = Section1.conjugateCharacter Γ)
    (hΓone : Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0)
    (hΔfacts : section14_theorem_14_9_late_type_T1DeltaParityFactsSourceData Γ T1) :
    section14_theorem_14_9_late_type_T1DeltaEvenScalarProductSourceData Γ T1 := by
  intro χ hχ Δ hΔcorr
  rcases hΔfacts χ hχ Δ hΔcorr with ⟨hΔvirt, hΔreal, _hΔone⟩
  exact section14_real_virtual_principal_orthogonal_scalarProduct_even_source_bridge
    hΓvirt hΓreal hΓone hΔvirt hΔreal

@[expose] public def section14_theorem_14_9_late_type_T1DeltaEquationSourceData
    {G : Type u} [Group G] [Finite G]
    (Γ : Section1.ClassFunction G)
    (T1 : Finset (Section1.ClassFunction G)) : Prop :=
  ∀ χ ∈ T1,
    ∃ Δ : Section1.ClassFunction G, ∃ m : ℤ,
      Section1.scalarProduct G Γ Δ = ((2 * m : ℤ) : ℂ) ∧
        (0 : ℂ) =
          1 - Section1.scalarProduct G Γ χ + Section1.scalarProduct G Γ Δ

public theorem section14_theorem_14_9_late_type_T1DeltaEquationSourceData_of_correction_even
    {G : Type u} [Group G] [Finite G]
    {Γ : Section1.ClassFunction G}
    {T1 : Finset (Section1.ClassFunction G)}
    (hcorr : section14_theorem_14_9_late_type_T1DeltaCorrectionSourceData Γ T1)
    (heven : section14_theorem_14_9_late_type_T1DeltaEvenScalarProductSourceData Γ T1) :
    section14_theorem_14_9_late_type_T1DeltaEquationSourceData Γ T1 := by
  intro χ hχ
  rcases hcorr χ hχ with ⟨Δ, hΔcorr⟩
  rcases heven χ hχ Δ hΔcorr with ⟨m, hΔeven⟩
  exact ⟨Δ, m, hΔeven, hΔcorr.1⟩

public theorem section14_theorem_14_9_late_type_T1ParityEquationSourceData_of_deltaEquation
    {G : Type u} [Group G] [Finite G]
    {Γ : Section1.ClassFunction G}
    {T1 : Finset (Section1.ClassFunction G)}
    (hsrc : section14_theorem_14_9_late_type_T1DeltaEquationSourceData Γ T1) :
    section14_theorem_14_9_late_type_T1ParityEquationSourceData Γ T1 := by
  intro χ hχ
  rcases hsrc χ hχ with ⟨Δ, m, hDeltaEven, hDeltaEq⟩
  refine ⟨m, ?_⟩
  simpa [hDeltaEven] using hDeltaEq

public theorem section14_theorem_14_9_late_type_T1EvenRemainderSourceData_of_parityEquation
    {G : Type u} [Group G] [Finite G]
    {Γ : Section1.ClassFunction G}
    {T1 : Finset (Section1.ClassFunction G)}
    (hsrc : section14_theorem_14_9_late_type_T1ParityEquationSourceData Γ T1) :
    section14_theorem_14_9_late_type_T1EvenRemainderSourceData Γ T1 := by
  intro χ hχ
  rcases hsrc χ hχ with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  let z := Section1.scalarProduct G Γ χ
  let e : ℂ := ((2 * m : ℤ) : ℂ)
  have hzero : 1 - z + e = 0 := by
    simpa [z, e] using hm.symm
  calc
    Section1.scalarProduct G Γ χ - 1 = e - (1 - z + e) := by
      dsimp [z, e]
      ring
    _ = e - 0 := by rw [hzero]
    _ = ((2 * m : ℤ) : ℂ) := by
      dsimp [e]
      ring

public theorem section14_oddScalarProduct_of_sub_one_eq_even_integer
    {z : ℂ}
    (heven : ∃ m : ℤ, z - 1 = ((2 * m : ℤ) : ℂ)) :
    Section13.oddScalarProduct z := by
  rcases heven with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  change (2 * (m : ℂ) + 1 : ℂ) = z
  calc
    (2 * (m : ℂ) + 1 : ℂ) = ((2 * m : ℤ) : ℂ) + 1 := by norm_num
    _ = (z - 1) + 1 := by rw [← hm]
    _ = z := by ring


@[expose] public def section14_theorem_14_9_late_type_T1ImageDeltaSourceData
    {G : Type u} [Group G] [Finite G]
    (Tmax : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (Γ : Section1.ClassFunction G)
    (p q v : ℕ) : Prop :=
  ∃ (T1T : Finset (Section1.ClassFunction Tmax))
    (τT1 : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G),
    ((v - 1 : ℕ) : ℝ) / (p : ℝ) ≤ (T1T.card : ℝ) ∧
      (∀ ζ ∈ T1T, Section1.scalarProduct Tmax ζ ζ = 1) ∧
      (∀ ζ ∈ T1T, ∀ ξ ∈ T1T, ζ ≠ ξ →
        Section1.scalarProduct Tmax ζ ξ = 0) ∧
      Section6.coherentExtension T1T τT τT1 ∧
      (∀ ζ ∈ T1T, ∀ i k : ℕ, i < q → k < p →
        Section1.scalarProduct G (η i k) (τT1 ζ) = 0) ∧
      (∀ ζ ∈ T1T,
        ∃ Δ : Section1.ClassFunction G,
          section14_theorem_14_9_late_type_T1DeltaCorrection Γ (τT1 ζ) Δ)


public theorem section14_theorem_14_9_late_type_T1SourceData_of_imageDeltaSourceData
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Tmax : Subgroup G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {Γ : Section1.ClassFunction G}
    {p q v : ℕ}
    (hΓvirt : Theory.Character.IsVirtualCharacter Γ)
    (hΓreal : Γ = Section1.conjugateCharacter Γ)
    (hΓone : Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0)
    (hsrc : section14_theorem_14_9_late_type_T1ImageDeltaSourceData Tmax τT η Γ p q v) :
    section14_theorem_14_9_late_type_T1SourceData η Γ p q v := by
  classical
  rcases hsrc with
    ⟨T1T, τT1, hcard, hselfT, horthT, hcohT1, hηorthT, hDeltaT⟩
  rcases hcohT1 with ⟨hIsoT1, _hVirtT1, _hAgreeT1⟩
  let T1 : Finset (Section1.ClassFunction G) := T1T.image τT1
  have hinjOn : Set.InjOn (fun ζ : Section1.ClassFunction Tmax => τT1 ζ) (↑T1T : Set _) := by
    intro ζ hζ ξ hξ hmap
    by_contra hne
    have hselfG :
        Section1.scalarProduct G (τT1 ζ) (τT1 ζ) = 1 := by
      rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem hIsoT1 hζ hζ]
      exact hselfT ζ hζ
    have hcrossG :
        Section1.scalarProduct G (τT1 ζ) (τT1 ξ) = 0 := by
      rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem hIsoT1 hζ hξ]
      exact horthT ζ hζ ξ hξ hne
    change τT1 ζ = τT1 ξ at hmap
    rw [← hmap] at hcrossG
    rw [hselfG] at hcrossG
    exact one_ne_zero hcrossG
  have hcardImage : T1.card = T1T.card := by
    dsimp [T1]
    exact Finset.card_image_of_injOn hinjOn
  have hDeltaCorr :
      section14_theorem_14_9_late_type_T1DeltaCorrectionSourceData Γ T1 := by
    intro χ hχ
    rcases Finset.mem_image.mp hχ with ⟨ζ, hζ, rfl⟩
    exact hDeltaT ζ hζ
  have hDeltaFacts :
      section14_theorem_14_9_late_type_T1DeltaParityFactsSourceData Γ T1 := by
    intro χ hχ Δ hΔcorr
    exact ⟨hΔcorr.2.1, hΔcorr.2.2.1, hΔcorr.2.2.2⟩
  have hDeltaEven :
      section14_theorem_14_9_late_type_T1DeltaEvenScalarProductSourceData Γ T1 :=
    section14_theorem_14_9_late_type_T1DeltaEvenScalarProductSourceData_of_parityFacts
      hΓvirt hΓreal hΓone hDeltaFacts
  have hDeltaEquation :
      section14_theorem_14_9_late_type_T1DeltaEquationSourceData Γ T1 :=
    section14_theorem_14_9_late_type_T1DeltaEquationSourceData_of_correction_even
      hDeltaCorr hDeltaEven
  have hParity :
      section14_theorem_14_9_late_type_T1ParityEquationSourceData Γ T1 :=
    section14_theorem_14_9_late_type_T1ParityEquationSourceData_of_deltaEquation
      hDeltaEquation
  have hEvenRemainder :
      section14_theorem_14_9_late_type_T1EvenRemainderSourceData Γ T1 :=
    section14_theorem_14_9_late_type_T1EvenRemainderSourceData_of_parityEquation
      hParity
  refine ⟨T1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcardImage]
    exact hcard
  · intro χ hχ
    rcases Finset.mem_image.mp hχ with ⟨ζ, hζ, rfl⟩
    rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem hIsoT1 hζ hζ]
    exact hselfT ζ hζ
  · intro χ hχ ψ hψ hne
    rcases Finset.mem_image.mp hχ with ⟨ζ, hζ, rfl⟩
    rcases Finset.mem_image.mp hψ with ⟨ξ, hξ, rfl⟩
    have hζξ : ζ ≠ ξ := by
      intro hEq
      exact hne (by rw [hEq])
    rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem hIsoT1 hζ hξ]
    exact horthT ζ hζ ξ hξ hζξ
  · intro χ hχ i k hi hk
    rcases Finset.mem_image.mp hχ with ⟨ζ, hζ, rfl⟩
    exact hηorthT ζ hζ i k hi hk
  · intro χ hχ
    exact section14_oddScalarProduct_of_sub_one_eq_even_integer
      (hEvenRemainder χ hχ)

public theorem section14_theorem_14_9_late_type_T1ContributionData_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {Γ : Section1.ClassFunction G}
    {p q v : ℕ}
    (hsrc : section14_theorem_14_9_late_type_T1SourceData η Γ p q v) :
    section14_theorem_14_9_late_type_T1ContributionData η Γ p q v := by
  rcases hsrc with ⟨T1, hcard, hself, horthNe, hηorth, hΓodd⟩
  refine ⟨T1, hcard, hself, horthNe, hηorth, ?_⟩
  intro χ hχ
  exact section14_normSq_ge_one_of_oddScalarProduct (hΓodd χ hχ)

end CFSG.Section14

module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: basic notation

This file records book-facing vocabulary for Peterfalvi, Section 13,
`The Subgroups S and T`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe u

/-- The preimage in a subgroup of an ambient book-facing subset. -/
@[expose] public def subgroupSetPreimage
    {G : Type u} [Group G]
    (M : Subgroup G) (A : Set G) : Set M :=
  {x : M | (x : G) ∈ A}

/-- The PF/FT Type-P support set `A₀(M) = A(M) ∪ 𝒞_M(Ẇ)` used in
Peterfalvi Sections 8 and 13.

This is deliberately separate from the early BG Section 16 set
`section16AZeroSet`, whose Lean name records the older definition
`\widehat M_\sigma - C_M(K#)`. -/
@[expose] public def typePFAZeroSet
    {G : Type u} [Group G]
    (M W1 W2 MF : Subgroup G) : Set G :=
  Section8.section8CentralizerUnion (ambientDerivedSubgroup M) MF ∪
    section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)


public theorem fittingPunctured_subset_typePFAZeroSet_of_typePDefinitionData
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    section16NonidentityElements (section8FittingSubgroup M : Set G) ⊆
      typePFAZeroSet M W1 W2 MF := by
  classical
  intro x hx
  rcases hx with ⟨hxF, hxne⟩
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, hMFnotcyc, _hM2le, hFitEq, hFitLeD, _hW2le,
      _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases hMF.1 with ⟨hMFM, hMFNormalM, _hMFnil, _hMFHallM⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  let C : Subgroup G := subgroupCentralizerIn M MF
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hFleM : section8FittingSubgroup M ≤ M := hFitLeD.trans hDleM
  have hCleM : C ≤ M := by
    intro y hy
    exact hy.1
  have hsupM :
      MF.subgroupOf M ⊔ C.subgroupOf M =
        (section8FittingSubgroup M).subgroupOf M := by
    calc
      MF.subgroupOf M ⊔ C.subgroupOf M = (MF ⊔ C).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := MF) (A' := C) (B := M) hMFM hCleM
      _ = (section8FittingSubgroup M).subgroupOf M := by
        rw [hFitEq]
  let xM : M := ⟨x, hFleM hxF⟩
  have hxSupM : xM ∈ MF.subgroupOf M ⊔ C.subgroupOf M := by
    rw [hsupM]
    exact hxF
  letI : (MF.subgroupOf M).Normal := hMFNormalM
  rcases (Subgroup.mem_sup_of_normal_left (s := MF.subgroupOf M)
      (t := C.subgroupOf M) (x := xM)).1 hxSupM with
    ⟨mM, hmMFsub, cM, hcCsub, hmulM⟩
  let m : G := mM
  let c : G := cM
  have hmMF : m ∈ MF := by
    simpa [m, Subgroup.mem_subgroupOf] using hmMFsub
  have hcC : c ∈ C := by
    simpa [c, C, Subgroup.mem_subgroupOf] using hcCsub
  have hmul : m * c = x := by
    simpa [m, c, xM] using congrArg Subtype.val hmulM
  have hxD : x ∈ D := hFitLeD hxF
  left
  by_cases hmne : m = 1
  · have hMFne : MF ≠ ⊥ := by
      intro hbot
      exact hMFnotcyc (by subst hbot; infer_instance)
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hMFne with ⟨zMF, hzMFne⟩
    let z : G := zMF
    have hzMF : z ∈ MF := zMF.property
    have hzne : z ≠ 1 := by
      intro hz
      exact hzMFne (Subtype.ext hz)
    have hxc : x = c := by
      rw [← hmul, hmne, one_mul]
    have hcent : x ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hxc]
      exact (Subgroup.mem_centralizer_iff.mp hcC.2 z hzMF).symm
    refine ⟨z, ⟨hzMF, hzne⟩, ?_⟩
    exact ⟨by simpa [D, elementCentralizerIn] using And.intro hxD hcent, hxne⟩
  · have hcent_m : c * m = m * c :=
      (Subgroup.mem_centralizer_iff.mp hcC.2 m hmMF).symm
    have hxcent : x ∈ Subgroup.centralizer ({m} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hmul]
      calc
        (m * c) * m = m * (c * m) := by simp [mul_assoc]
        _ = m * (m * c) := by rw [hcent_m]
    refine ⟨m, ⟨hmMF, hmne⟩, ?_⟩
    exact ⟨by simpa [D, elementCentralizerIn] using And.intro hxD hxcent, hxne⟩

/-- The PF Section 13 family
`{Ind_H^M θ | θ ∈ Irr H, K` is not contained in `Ker θ`}`. -/
@[expose] public def nonkernelInducedFamily
    {G : Type u} [Group G] [Finite G]
    (M H K : Subgroup G)
    (F : Finset (Section1.ClassFunction M)) : Prop :=
  H ≤ M ∧ K ≤ H ∧
    ∀ χ : Section1.ClassFunction M,
      χ ∈ F ↔
        ∃ θ : Section1.ClassFunction (H.subgroupOf M),
          Section1.IsIrreducibleCharacterOnGroup θ ∧
            ¬ Section1.subgroupInKernel' θ
              ((K.subgroupOf M).subgroupOf (H.subgroupOf M)) ∧
            χ = Section1.inducedCF (H.subgroupOf M) θ

/-- The PF Section 13 nonkernel-induced family is finite: take the irreducible
characters of the inducing subgroup whose kernels do not contain `K`, then
induce them to `M`. -/
public theorem exists_nonkernelInducedFamily
    {G : Type u} [Group G] [Finite G]
    (M H K : Subgroup G)
    (hHM : H ≤ M)
    (hKH : K ≤ H) :
    ∃ S : Finset (Section1.ClassFunction M),
      nonkernelInducedFamily M H K S := by
  classical
  rcases Theory.Character.irreducible_characters_form_basis (G := H.subgroupOf M) with
    ⟨ι, hι, χ, hχ, _b, _hb⟩
  letI : Fintype ι := hι
  let ψ : ι → Section1.ClassFunction (H.subgroupOf M) :=
    fun i => Section1.ofConjClassFunction (χ i)
  let S : Finset (Section1.ClassFunction M) :=
    (Finset.univ.filter
        (fun i : ι => ¬ Section1.subgroupInKernel' (ψ i)
          ((K.subgroupOf M).subgroupOf (H.subgroupOf M)))).image
      (fun i => Section1.inducedCF (H.subgroupOf M) (ψ i))
  refine ⟨S, hHM, hKH, ?_⟩
  intro η
  constructor
  · intro hη
    rcases Finset.mem_image.mp hη with ⟨i, hi, rfl⟩
    have hirr : Section1.IsIrreducibleCharacterOnGroup (ψ i) :=
      Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 i)
    have hnotker : ¬ Section1.subgroupInKernel' (ψ i)
        ((K.subgroupOf M).subgroupOf (H.subgroupOf M)) :=
      (Finset.mem_filter.mp hi).2
    exact ⟨ψ i, hirr, hnotker, rfl⟩
  · rintro ⟨θ, hθirr, hθnotker, rfl⟩
    have hθclass : Section1.IsClassFunction θ :=
      Section1.isCharacter_isClassFunction θ
        (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
    have hθrepirr : Theory.Character.IsIrreducibleConjCharacter
        (Section1.toConjClassFunction θ hθclass) := by
      rcases hθirr with ⟨n, ρ, hρ, rfl⟩
      refine ⟨?_, ?_⟩
      · exact ⟨n, ρ, rfl⟩
      · rw [Section1.classFunctionInner_toConjClassFunction]
        exact Section1.scalarProduct_representation_char_self
          (G := H.subgroupOf M) ρ hρ
    rcases hχ.2.1 (Section1.toConjClassFunction θ hθclass) hθrepirr with
      ⟨i, hi⟩
    have hψθ : ψ i = θ := by
      ext h
      change χ i (ConjClasses.mk h) = θ h
      rw [hi]
      rfl
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ i, by simpa [hψθ] using hθnotker⟩
    · rw [hψθ]


@[expose] public noncomputable def section13_irreducibleSubfamily
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (F : Finset (Section1.ClassFunction M)) :
    Finset (Section1.ClassFunction M) := by
  classical
  exact F.filter fun φ => Section1.IsIrreducibleCharacterOnGroup φ

public theorem section13_irreducibleSubfamily_subset
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (F : Finset (Section1.ClassFunction M)) :
    section13_irreducibleSubfamily M F ⊆ F := by
  classical
  intro φ hφ
  change φ ∈ F.filter (fun φ => Section1.IsIrreducibleCharacterOnGroup φ) at hφ
  exact (Finset.mem_filter.mp hφ).1


/-- The PF13 Dade map on the nonkernel induced family.

The carrier relevant to this family is the punctured integral span from
Hypothesis `(5.2)(b)`.  The book and prime-Dade carriers attached to a selected
Type-P witness are recorded separately in `typePFourSixTauSourceData`. -/
@[expose] public def dadeIsometryRelativeToAZero
    {G : Type u} [Group G] [Finite G]
    (M _K : Subgroup G)
    (F : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Section5.hypothesis_5_2_b_statement F τ

/-- The ambient value-agreement part of the Type-P Section `(4.6)` package.
It records that the chosen global Dade map preserves values on the cyclic-TI
set after viewing the cyclic-TI data inside the maximal subgroup `M`. -/
@[expose] public def typePFourSixSigmaAgreesOnCyclicTI
    {G : Type u} [Group G] [Finite G]
    (M W1 W2 : Subgroup G)
    (W : Subgroup M)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ α : Section1.ClassFunction W,
    Section1.IsClassFunction α →
      ∀ x : M, ∀ hx : x ∈
        Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W,
          σ α (x : G) =
            α ⟨x, Section3.cyclicTISet_subset
              (W1.subgroupOf M) (W2.subgroupOf M) W hx⟩


@[expose] public def typePFourSixTauSourceData
    {G : Type u} [Group G] [Finite G]
    (M MF _U W1 W2 : Subgroup G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
    ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
        ∃ μ : I → J → Section1.ClassFunction M,
          ∃ δSign : J → ℤ,
            ∃ ω : I → J → Section1.ClassFunction W,
              ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
                @Section10.section10FourSixNotationSupportedData G _ _ I J instI instJ
                  decI decJ M W1 W2 W A
                  A0 i0 j0 μ δSign ω σ τ ∧
                typePFourSixSigmaAgreesOnCyclicTI M W1 W2 W σ ∧
                ∃ H_cyclicA0 : G → Subgroup G,
                  ∃ hCyclicA0 :
                    Section2.hypothesis_2_2_statement
                      (Section4Scratch.subgroupImageSet M
                        (Section4Scratch.primeDadeA0Set
                          (W1.subgroupOf M) (W2.subgroupOf M) W A))
                      M H_cyclicA0,
                    (∀ α : Section1.ClassFunction M,
                      Section2.CFOn M
                          (Section4Scratch.subgroupImageSet M
                            (Section4Scratch.primeDadeA0Set
                              (W1.subgroupOf M) (W2.subgroupOf M) W A)) α →
                        τ α =
                          Section2.dadeTransform H_cyclicA0
                            hCyclicA0.subset_L α) ∧
                ∃ Ms : Subgroup G, ∃ Abook A0book A1book : Set G,
                  ∃ H_A0 : G → Subgroup G,
                    ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
                    Section8.notation_8_10_source_data M MF Ms Abook A0book A1book ∧
                    Abook = Section8.section8CentralizerUnion
                      (ambientDerivedSubgroup M) Ms ∧
                    A0book =
                      Abook ∪ section16ConjugatesOfSetBySet
                        (section16HatW W1 W2) (M : Set G) ∧
                    MF ≤ Ms ∧
                    (∀ l : M,
                      (l : G) ∈
                        section16NonidentityElements ((Ms : Subgroup G) : Set G) →
                          (l : G) ∈ A0book) ∧
                    ∀ α : Section1.ClassFunction M,
                      τ α = Section2.dadeTransform H_A0 hA0M.subset_L α

/-- The PF `(13.2)(e)` type-P support assertion: the chosen Dade isometry
agrees with induction on class functions supported on the PF/FT type-P
realization of `A₀(M)`. The first conjunct is kept as a stable projection
slot for older consumers; the mathematical content is the type-P universal
field. -/
@[expose] public def agreesWithInductionOnAZero
    {G : Type u} [Group G] [Finite G]
    (M K _U W1 W2 : Subgroup G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  True ∧
    ∀ χ : Section1.ClassFunction M,
      Section2.CFOn M (typePFAZeroSet M W1 W2 K) χ →
        τ χ = Section1.inducedCFLinear M χ

/-- The book-facing PF `(13.2)(e)` induction agreement for the actual
Section `(4.6)` `A₀(M)` package used in Types III/IV/V.

The witness includes the selected PF `(8.10)` subgroup `M_s`, the source Dade
transform package, the TI-with-normalizer fact for the same book `A₀(M)`, and
the three source-exact support inclusions used downstream: `M_s#`, `F(M)#`,
and the Type-P set `A(M)`. -/
@[expose] public def agreesWithInductionOnBookAZero
    {G : Type u} [Group G] [Finite G]
    (M MF U _W1 _W2 : Subgroup G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ Ms : Subgroup G, ∃ A0book : Set G, ∃ H_A0 : G → Subgroup G,
    ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
      Section8.msChoiceSource M MF Ms ∧
        section16TISubsetWithNormalizer A0book M ∧
        (∀ l : M,
          (l : G) ∈ section16NonidentityElements ((Ms : Subgroup G) : Set G) →
            (l : G) ∈ A0book) ∧
        (∀ l : M,
          (l : G) ∈
              section16NonidentityElements (section8FittingSubgroup M : Set G) →
            (l : G) ∈ A0book) ∧
        section16ASet M U ⊆ A0book ∧
        (∀ α : Section1.ClassFunction M,
          τ α = Section2.dadeTransform H_A0 hA0M.subset_L α) ∧
        ∀ χ : Section1.ClassFunction M,
          Section2.CFOn M A0book χ →
            τ χ = Section1.inducedCFLinear M χ

/-- The PF `(13.1)(d)` `ωᵢⱼ` notation from PF `(3.3)`, indexed by
natural numbers in the Section 13 range.  The phrase "as in `(3.3)`"
also carries the standing PF `(3.1)` cyclic-TI hypotheses for `W`. -/
@[expose] public def hypothesis_13_1_omegaNotationData
    {G : Type u} [Group G] [Finite G]
    (W W1 W2 : Subgroup G)
    (p q : ℕ)
    (ω : ℕ → ℕ → Section1.ClassFunction W) : Prop :=
  Section3.hypothesis_3_1_statement W1 W2 W ∧
    ∃ (hq : 0 < q) (hp : 0 < p)
      (ωFin : Fin q → Fin p → Section1.ClassFunction W),
        Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
          ⟨0, hq⟩ ⟨0, hp⟩ ωFin ∧
          ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
            ω i j = ωFin ⟨i, hi⟩ ⟨j, hj⟩

/-- The character notation introduced in PF `(13.1)(d,e)`: the families
`ωᵢⱼ`, `ηᵢⱼ`, `μᵢⱼ`, `νᵢⱼ`, the signs `δⱼ`, `δ'ᵢ`, and the row/column sums. -/
@[expose] public def hypothesis_13_1_characterNotationDataFor
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (p q : ℕ)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_13_1_omegaNotationData W W1 W2 p q ω ∧
    Section3.theorem_3_2_map_statement W1 W2 W σ ∧
    (∀ i j, i < q → j < p → η i j = σ (ω i j)) ∧
    (∀ j, j < p → δ j = 1 ∨ δ j = -1) ∧
    (∀ i, i < q → δ' i = 1 ∨ δ' i = -1) ∧
    (∀ i j, i < q → j < p →
      Section1.IsIrreducibleCharacterOnGroup (μ i j)) ∧
    (∀ i j, i < q → j < p →
      Section1.IsIrreducibleCharacterOnGroup (ν i j)) ∧
    (∀ j, 0 < j → j < p →
      μ 0 j ≠ Section1.principalCharacter Smax) ∧
    (∀ i, 0 < i → i < q →
      ν i 0 ≠ Section1.principalCharacter Tmax) ∧
    (∀ i j, i < q → j < p →
      Section1.inducedCF (W.subgroupOf Smax)
          (Section1.subgroupOfClassFunction (T := Smax) (ω i j - ω 0 j)) =
        (((δ j : ℤ) : ℂ) • (μ i j - μ 0 j))) ∧
    (∀ i j, i < q → j < p →
      Section1.inducedCF (W.subgroupOf Tmax)
          (Section1.subgroupOfClassFunction (T := Tmax) (ω i j - ω i 0)) =
        (((δ' i : ℤ) : ℂ) • (ν i j - ν i 0))) ∧
    (∀ j, j < p → μsum j = (Finset.range q).sum (fun i => μ i j)) ∧
    (∀ i, i < q → νsum i = (Finset.range p).sum (fun j => ν i j)) ∧
    (((δ 0 : ℤ) : ℂ) • μ 0 0 = Section1.principalCharacter Smax) ∧
    (((δ' 0 : ℤ) : ℂ) • ν 0 0 = Section1.principalCharacter Tmax) ∧
    (∀ j k, 0 < j → j < p → 0 < k → k < p →
      Section1.degree (μ 0 j) = Section1.degree (μ 0 k)) ∧
    (∀ i k, 0 < i → i < q → 0 < k → k < q →
      Section1.degree (ν i 0) = Section1.degree (ν k 0))

/-- The character notation introduced in PF `(13.1)(d,e)`: the families
`ωᵢⱼ`, `ηᵢⱼ`, `μᵢⱼ`, `νᵢⱼ`, the signs `δⱼ`, `δ'ᵢ`, and the row/column sums. -/
@[expose] public def hypothesis_13_1_characterNotationData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (p q : ℕ) : Prop :=
  ∃ (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ


@[expose] public def hypothesis_13_1_dadeDifferenceDataFor
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ) : Prop :=
  ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
          ω η μ ν μsum νsum δ δ' σ →
        (∀ i j k, i < q → 0 < j → j < p → 0 < k → k < p →
          Section1.degree (μ i j) = Section1.degree (μ i k) →
          τS (μ i j - μ i k) =
            (((δ j : ℤ) : ℂ) • (σ (ω i j) - σ (ω i k)))) ∧
        (∀ i k j, 0 < i → i < q → 0 < k → k < q → j < p →
          Section1.degree (ν i j) = Section1.degree (ν k j) →
          τT (ν i j - ν k j) =
            (((δ' i : ℤ) : ℂ) • (σ (ω i j) - σ (ω k j))))


@[expose] public def hypothesis_13_1_zeroBaseDegreeDataFor
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (p q : ℕ) : Prop :=
  ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
          ω η μ ν μsum νsum δ δ' σ →
        (∀ j k, 0 < j → j < p → 0 < k → k < p →
          Section1.degree (μ 0 j) = Section1.degree (μ 0 k)) ∧
        (∀ i k, 0 < i → i < q → 0 < k → k < q →
          Section1.degree (ν i 0) = Section1.degree (ν k 0))


@[expose] public def hypothesis_13_1_conjugateIndexDataFor
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (p q : ℕ) : Prop :=
  ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
          ω η μ ν μsum νsum δ δ' σ →
        (∀ j, 0 < j → j < p →
          ∃ k : ℕ, 0 < k ∧ k < p ∧ k ≠ j ∧
            η 0 k = Section1.conjugateCharacter (η 0 j) ∧
              μ 0 k = Section1.conjugateCharacter (μ 0 j)) ∧
        (∀ i, 0 < i → i < q →
          ∃ k : ℕ, 0 < k ∧ k < q ∧ k ≠ i ∧
            η k 0 = Section1.conjugateCharacter (η i 0) ∧
              ν k 0 = Section1.conjugateCharacter (ν i 0))


@[expose] public def hypothesis_13_1_conjugateBetaTauDataFor
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ) : Prop :=
  ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
          ω η μ ν μsum νsum δ δ' σ →
        (∀ j k, 0 < j → j < p → 0 < k → k < p →
          μ 0 k = Section1.conjugateCharacter (μ 0 j) →
            Section1.conjugateCharacter
                (τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                  (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                    μ 0 j)) =
              τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                  μ 0 k)) ∧
        (∀ i k, 0 < i → i < q → 0 < k → k < q →
          ν k 0 = Section1.conjugateCharacter (ν i 0) →
            Section1.conjugateCharacter
                (τT (Section1.inducedCF ((Q ⊔ W2).subgroupOf Tmax)
                  (Section1.principalCharacter ((Q ⊔ W2).subgroupOf Tmax)) -
                    ν i 0)) =
              τT (Section1.inducedCF ((Q ⊔ W2).subgroupOf Tmax)
                (Section1.principalCharacter ((Q ⊔ W2).subgroupOf Tmax)) -
                  ν k 0))

/-- The displayed support set `P# ∪ V_S` from the proof of PF `(13.18)`. -/
@[expose] public def theorem_13_18_betaSupportSet
    {G : Type u} [Group G]
    (Smax W W1 W2 P : Subgroup G) : Set G :=
  (section16NonidentityElements (P : Set G)) ∪
    section16ConjugatesOfSetBySet
      ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (Smax : Set G)


@[expose] public def hypothesis_13_1_betaSupportNormDataFor
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q : Subgroup G)
    (p q u v : ℕ) : Prop :=
  (∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax) (j : ℕ),
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
          ω η μ ν μsum νsum δ δ' σ →
        0 < j →
          j < p →
            βS = Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                  μ 0 j →
              Section1.supportedOn βS
                  (subgroupSetPreimage Smax
                    (theorem_13_18_betaSupportSet Smax W W1 W2 P)) ∧
                Section5.cfNormSq βS = ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 2) ∧
    (∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
      (βT : Section1.ClassFunction Tmax) (i : ℕ),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          0 < i →
            i < q →
              βT = Section1.inducedCF ((Q ⊔ W2).subgroupOf Tmax)
                  (Section1.principalCharacter ((Q ⊔ W2).subgroupOf Tmax)) -
                    ν i 0 →
                Section1.supportedOn βT
                    (subgroupSetPreimage Tmax
                      (theorem_13_18_betaSupportSet Tmax W W2 W1 Q)) ∧
                  Section5.cfNormSq βT = ((v - 1 : ℕ) : ℝ) / (p : ℝ) + 2)

/-- The PF `(8.10)` source choice convention for maximal subgroups whose PF
source type has been identified. -/
@[expose] public def hypothesis_13_1_sourceChoiceData
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
    section16MFSubgroup M MF →
      (Section8.typeIDefinitionData M MF ∨
        Section8.typeIIDefinitionData M MF ∨
          Section8.typeIIIDefinitionData M MF ∨
            Section8.typeIVDefinitionData M MF ∨
              Section8.typeVDefinitionData M MF) →
        ∃ Ms : Subgroup G, Section8.msChoiceSource M MF Ms

/-- PF Hypothesis `(13.1)`. -/
@[expose] public def hypothesis_13_1_data
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) : Prop :=
  Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q ∧
    Section8.typePData Smax P U W1 W2 ∧
    Section8.typePData Tmax Q V W2 W1 ∧
    W = W1 ⊔ W2 ∧
    p = Nat.card W2 ∧
    q = Nat.card W1 ∧
    C = subgroupCentralizerIn U P ∧
    D = subgroupCentralizerIn V Q ∧
    Nat.card U = u * c ∧
    Nat.card V = v * d ∧
    Section5.hypothesis_5_2_b_statement Sfam τS ∧
    Section5.hypothesis_5_2_b_statement Tfam τT ∧
    c = Nat.card C ∧
    d = Nat.card D

/-- The full source-level content of PF Hypothesis `(13.1)`, extending the
structural data used elsewhere in the project with the exact induced-family,
Dade-isometry, character-notation clauses from the text, and the standing
minimal-counterexample context carried into Section 13 by PF `(12.17)`. -/
@[expose] public def hypothesis_13_1_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) : Prop :=
  Section8.theorem_8_8_source_case_b_data W W1 W2 Smax Tmax P Q ∧
    Section8.typePDefinitionData Smax P U W1 W2 ∧
    Section8.typePDefinitionData Tmax Q V W2 W1 ∧
    p = Nat.card W2 ∧
    q = Nat.card W1 ∧
    C = subgroupCentralizerIn U P ∧
    D = subgroupCentralizerIn V Q ∧
    c = Nat.card C ∧
    d = Nat.card D ∧
    Nat.card U = u * c ∧
    Nat.card V = v * d ∧
    nonkernelInducedFamily Smax (P ⊔ U) P Sfam ∧
    nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam ∧
    dadeIsometryRelativeToAZero Smax P Sfam τS ∧
    dadeIsometryRelativeToAZero Tmax Q Tfam τT ∧
    hypothesis_13_1_characterNotationData Smax Tmax W W1 W2 p q ∧
    hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2 τS τT p q ∧
    hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2 p q ∧
    hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2 p q ∧
    hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2 P Q τS τT p q ∧
    hypothesis_13_1_sourceChoiceData G ∧
    IsMinCE G ∧
    typePFourSixTauSourceData Smax P U W1 W2 τS ∧
    typePFourSixTauSourceData Tmax Q V W2 W1 τT

/-- The case `(9.7)(b)` information as reused in Section 13. -/
@[expose] public def case_9_7_b_for_section13
    {G : Type u} [Group G] [Finite G]
    (M C : Subgroup G)
    (p q u : ℕ) : Prop :=
  C ≤ M ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Coprime u (p - 1) ∧
    u ∣ (p ^ q - 1) / (p - 1)

/-- The linear-character induction condition reused in PF `(13.10)`. -/
@[expose] public def inducedFromLinearCharacterForSection13
    {G : Type u} [Group G] [Finite G]
    (M N : Subgroup G)
    (χ : Section1.ClassFunction M) : Prop :=
  N ≤ M ∧
    ∃ θ : Section1.ClassFunction (N.subgroupOf M),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.degree θ = (1 : ℂ) ∧
        χ = Section1.inducedCF (N.subgroupOf M) θ

/-- The linear-induced character hypothesis from PF `(13.10)`. -/
@[expose] public def theorem_13_10_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax P C : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (_p q u : ℕ) : Prop :=
  ∃ lam : Section1.ClassFunction Smax,
    lam ∈ Sfam ∧
      Section1.IsIrreducibleCharacterOnGroup lam ∧
      Section1.degree lam = (u * q : ℂ) ∧
      inducedFromLinearCharacterForSection13 Smax (P ⊔ C) lam

/-- A class function on `H` is the restriction of one on the overgroup `M`. -/
@[expose] public def classFunctionRestrictionData
    {G : Type u} [Group G]
    (H M : Subgroup G)
    (φM : Section1.ClassFunction M)
    (φH : Section1.ClassFunction H) : Prop :=
  ∃ hHM : H ≤ M,
    ∀ x : H, φH x = φM ⟨(x : G), hHM x.property⟩

/-- Every irreducible constituent of a virtual character has `P` in its kernel. -/
@[expose] public def virtualCharacterKernelConstituentData
    {G : Type u} [Group G] [Finite G]
    (H P : Subgroup G)
    (α : Section1.ClassFunction H) : Prop :=
  Theory.Character.IsVirtualCharacter α ∧
    ∀ θ : Section1.ClassFunction H,
      Section1.IsIrreducibleCharacterOnGroup θ →
        Section1.scalarProduct H α θ ≠ 0 →
          Section1.subgroupInKernel' θ (P.subgroupOf H)


/-- A normalized square-sum lower bound used in PF `(13.6)`--`(13.10)`. -/
@[expose] public def squareSumLowerBound
    {G : Type u} [Group G] [Finite G]
    (H : Set G)
    (χ : Section1.ClassFunction G)
    (bound : ℝ) : Prop :=
  bound ≤ Section7.supportEnergy H χ

/-- The sign-normalization package in PF `(13.3)(c)`. -/
@[expose] public def theorem_13_3_signNormalizationFor
    (p q : ℕ) (δ δ' : ℕ → ℤ) : Prop :=
  (∀ j, j < p → δ j = 1) ∧
    ∀ i, i < q → δ' i = 1


/-- The source sign alternative in PF `(13.3)(c)`, stated for the transformed
row sums rather than hiding the `ηᵢⱼ` equations. -/
@[expose] public def theorem_13_3_signAlternativeData
    {G : Type u} [Group G] [Finite G]
    (p q : ℕ)
    (μτ : ℕ → Section1.ClassFunction G)
    (η : ℕ → ℕ → Section1.ClassFunction G) : Prop :=
  (∀ j, 0 < j → j < p →
    μτ j = (Finset.range q).sum (fun i => η i j)) ∨
  (p = 3 ∧
    ∀ j, 0 < j → j < p →
      ∃ j', ({j, j'} : Finset ℕ) = {1, 2} ∧
        μτ j = -((Finset.range q).sum (fun i => η i j')))

/-- The explicit PF `(13.3)(a,c)` character output: the named `μ_j`
characters for `j ≥ 1`, their linear-source property, and the sign alternative
for their Dade transforms.  These are the reducible prime-TI column sums; PF
`(13.3)(a)` does not assert that they are irreducible. -/
@[expose] public def theorem_13_3_characterOutputFor
    {G : Type u} [Group G] [Finite G]
    (Smax P C : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u : ℕ)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (η : ℕ → ℕ → Section1.ClassFunction G) : Prop :=
  (∀ j, 0 < j → j < p →
    Section1.IsCharacter (μsum j) ∧
      Section1.degree (μsum j) = (u * q : ℂ) ∧
      inducedFromLinearCharacterForSection13 Smax (P ⊔ C) (μsum j) ∧
      μsum j ∈ Sfam) ∧
    theorem_13_3_signAlternativeData p q (fun j => τ1 (μsum j)) η


/-- The PF `(13.5)` setup: `H=PC`, the family `S₁` of induced characters
with `P` not in the kernel, the distinguished `ζ₀, ζ₁`, the orthogonality
condition, and the definition of `a`. -/
@[expose] public def theorem_13_5_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax H P C : Subgroup G)
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (χ : Section1.ClassFunction G)
    (a : ℂ) : Prop :=
  H = P ⊔ C ∧
    nonkernelInducedFamily Smax H P S1 ∧
    ζ0 ∈ S1 ∧ ζ1 ∈ S1 ∧ ζ0 ≠ ζ1 ∧
    Theory.Character.IsVirtualCharacter χ ∧
    a = Section1.scalarProduct G (τS (ζ1 - ζ0)) χ ∧
    ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 → ζ ≠ ζ0 → ζ ≠ ζ1 →
      Section1.scalarProduct G (τS (ζ - ζ0)) χ = 0

/-- The PF `(13.5)(b)` square-sum identity. -/
@[expose] public def theorem_13_5_squareSumFormula
    {G : Type u} [Group G] [Finite G]
    (Smax H : Subgroup G)
    (ζ1S : Section1.ClassFunction Smax)
    (ζ1H α : Section1.ClassFunction H)
    (χ : Section1.ClassFunction G)
    (a : ℂ) : Prop :=
  (Section7.supportEnergy (Section7.puncturedSubgroupSet H) χ : ℂ) =
    (a ^ 2 / (Section5.cfNormSq ζ1S : ℂ)) *
      ((Nat.card Smax : ℂ) - (ζ1S 1) ^ 2 / (Section5.cfNormSq ζ1S : ℂ)) -
        2 * a * ζ1H 1 * α 1 / (Section5.cfNormSq ζ1S : ℂ) +
          (Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α : ℂ)


/-- The source case `(9.7)(a)` specialized to the Section 13 situation
`H₀ = 1`, with `u = |U/C|`. -/
@[expose] public def case_9_7_a_sourceDataForSection13
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 C : Subgroup G)
    (p q u : ℕ) : Prop :=
  Section9.quotientBarUCardinality U C u ∧
    ∃ a : ℕ, Section9.case_9_7_a_data M MF U W1 W2 ⊥ C p q a

/-- The source case `(9.7)(b)` specialized to the Section 13 situation
`H₀ = 1`. -/
@[expose] public def case_9_7_b_sourceDataForSection13
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 C : Subgroup G)
    (p q u : ℕ) : Prop :=
  Section9.case_9_7_b_data M MF U W1 W2 ⊥ C p q u

/-- The setup of PF `(13.6)`: `H = PC`, `λ` is an irreducible character of
`S` of degree `uq` induced from a linear character of `H`, and `λτ` is its
image under the extended Dade isometry. -/
@[expose] public def theorem_13_6_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax H P C : Subgroup G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (_p q u : ℕ) : Prop :=
  H = P ⊔ C ∧
    Section1.IsIrreducibleCharacterOnGroup lam ∧
    Section1.degree lam = (u * q : ℂ) ∧
    inducedFromLinearCharacterForSection13 Smax H lam ∧
    lamτ = τ1 lam

/-- The source definition of `G₀` from PF `(13.9)`. -/
@[expose] public def theorem_13_9_G0Data
    {G : Type u} [Group G]
    (H Q : Subgroup G)
    (G0 : Set G) : Prop :=
  G0 =
    section16NonidentityElements (Set.univ : Set G) \
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ ∪
        section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ)

/-- The PF `(13.9)` setup: `H=PC`, `G₀` is the complement specified in the
text, and `λ` is as in `(13.6)`. -/
@[expose] public def theorem_13_9_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax H P C Q : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u : ℕ) : Prop :=
  theorem_13_9_G0Data H Q G0 ∧
    lam ∈ Sfam ∧
    theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u

/-- The source setup for PF `(13.18)`, including the choice `0 < j < p` and
the definition of `β_j`. -/
@[expose] public def theorem_13_18_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax P W1 : Subgroup G)
    (μ0j β : Section1.ClassFunction Smax)
    (j p : ℕ) : Prop :=
  0 < j ∧ j < p ∧
    β = Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ0j

/-- The PF `(13.18)(d)` decomposition of `Γ` into the span of the `ηᵢₖ` and an
orthogonal remainder. -/
@[expose] public def theorem_13_18_decompositionData
    {G : Type u} [Group G] [Finite G]
    (p q : ℕ)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (X Y : Section1.ClassFunction G) : Prop :=
  (∃ coeff : ℕ → ℕ → ℂ,
    X = (Finset.range q).sum fun i =>
      (Finset.range p).sum fun k => coeff i k • η i k) ∧
  ∀ i k : ℕ, i < q → k < p →
    Section1.scalarProduct G Y (η i k) = 0

/-- Oddness of a scalar product, written as congruence to `1` modulo `2`. -/
@[expose] public def oddScalarProduct (z : ℂ) : Prop :=
  z ∈ Set.range (fun n : ℤ => (2 * n + 1 : ℂ))

/-- The source setup for PF `(13.19)`: `L` is Type I with `H=L_F`, the
family `ℒ`, the Dade extension, the degree-`e` character `φ`, and the
definitions of `β_L` and `β_S`. -/
@[expose] public def theorem_13_19_hypothesis
    {G : Type u} [Group G] [Finite G]
    (L H Smax P W1 : Subgroup G)
    (Lfam : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τL τL1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (φτ : Section1.ClassFunction G)
    (μ01 : Section1.ClassFunction Smax)
    (βL βS : Section1.ClassFunction G)
    (e : ℕ) : Prop :=
  L ∈ section9MaximalSubgroups G ∧
    section16MFSubgroup L H ∧
    Section8.typeIDefinitionData L H ∧
    e = H.relIndex L ∧
    Section12.dadeIsometryRelativeToTypeIASet L H R τL ∧
    Section7.puncturedInducedFamily (H.subgroupOf L) Lfam ∧
    Section7.isCoherentExtension Lfam τL τL1 ∧
    φ ∈ Lfam ∧
    Section1.degree φ = (e : ℂ) ∧
    φτ = τL1 φ ∧
    βL = τL (Section1.inducedCF (H.subgroupOf L)
        (Section1.principalCharacter (H.subgroupOf L)) - φ) ∧
    βS = τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ01)

/-- The independence assertion in PF `(13.19)(c)`. -/
@[expose] public def theorem_13_19_independenceData
    {G : Type u} [Group G] [Finite G]
    (βL : Section1.ClassFunction G)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (p : ℕ) : Prop :=
  ∀ j k : ℕ, 0 < j → j < p → 0 < k → k < p →
    Section1.scalarProduct G βL (η 0 j) =
      Section1.scalarProduct G βL (η 0 k)

/-- The alternatives in PF `(13.19)(c)`. -/
@[expose] public def theorem_13_19_alternativeData
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (βL βS φ : Section1.ClassFunction G)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (p q u e : ℕ) : Prop :=
  (oddScalarProduct (Section1.scalarProduct G βS φ) ∧
      ((Nat.card H - 1 : ℕ) : ℝ) / (e : ℝ) ≤
        ((u - 1 : ℕ) : ℝ) / (q : ℝ)) ∨
    ((∀ j : ℕ, 0 < j → j < p →
        oddScalarProduct (Section1.scalarProduct G βL (η 0 j))) ∧
      p ≤ e)

end CFSG.Section13

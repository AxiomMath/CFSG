module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 5: basic notation

This file records the common formal vocabulary for Peterfalvi, Section 5,
`Coherence`.

No BG results are imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section5

universe u

/-- The punctured ambient set `G#`, represented on the ambient type itself. -/
@[expose] public def puncturedSet
    {G : Type u} [One G] : Set G :=
  {g : G | g ≠ 1}

/--
`χ ∈ Z[S]`: the class function `χ` is an integral linear combination of the
finite family `S`.
-/
@[expose] public def integerSpan
    {L : Type u} [Group L]
    (S : Finset (Section1.ClassFunction L))
    (χ : Section1.ClassFunction L) : Prop :=
  ∃ v : Section1.CoeffVector S,
    χ = Section1.evalCoeff (fun X : S => (X : Section1.ClassFunction L)) v

public theorem integerSpan_mono
    {L : Type u} [Group L]
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    (hsub : S₁ ⊆ S₂)
    {χ : Section1.ClassFunction L} :
    integerSpan S₁ χ → integerSpan S₂ χ := by
  classical
  rintro ⟨v, rfl⟩
  let w : Section1.CoeffVector S₂ := fun Y =>
    if hY : (Y : Section1.ClassFunction L) ∈ S₁ then v ⟨Y, hY⟩ else 0
  refine ⟨w, ?_⟩
  ext g
  have hsum := Finset.sum_subset
      (s₁ := S₁) (s₂ := S₂)
      (f := fun Y : Section1.ClassFunction L =>
        (((if hY : Y ∈ S₁ then v ⟨Y, hY⟩ else 0 : Int) : ℂ) * Y g))
      hsub
      (by
        intro Y _hY2 hY1
        simp [hY1])
  simpa +contextual [Section1.evalCoeff, w, smul_eq_mul, ← S₁.sum_attach,
    ← S₂.sum_attach] using hsum

public theorem integerSpan_of_mem
    {L : Type u} [Group L]
    (S : Finset (Section1.ClassFunction L))
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ S) :
    integerSpan S χ := by
  classical
  refine ⟨Section1.basisVector ⟨χ, hχ⟩, ?_⟩
  ext g
  rw [Section1.evalCoeff, Finset.sum_eq_single ⟨χ, hχ⟩]
  · simp [Section1.basisVector]
  · intro X _hX hXne
    simp [Section1.basisVector, hXne]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

public theorem integerSpan_add
    {L : Type u} [Group L]
    {S : Finset (Section1.ClassFunction L)}
    {φ ψ : Section1.ClassFunction L} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ + ψ) := by
  classical
  rintro ⟨v, rfl⟩ ⟨w, rfl⟩
  refine ⟨v + w, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.sum_add_distrib, add_mul]

public theorem integerSpan_neg
    {L : Type u} [Group L]
    {S : Finset (Section1.ClassFunction L)}
    {φ : Section1.ClassFunction L} :
    integerSpan S φ → integerSpan S (-φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  ext g
  simp [Section1.evalCoeff]

public theorem integerSpan_sub
    {L : Type u} [Group L]
    {S : Finset (Section1.ClassFunction L)}
    {φ ψ : Section1.ClassFunction L} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ - ψ) := by
  intro hφ hψ
  simpa [sub_eq_add_neg] using integerSpan_add hφ (integerSpan_neg hψ)

public theorem integerSpan_zsmul
    {L : Type u} [Group L]
    {S : Finset (Section1.ClassFunction L)}
    {φ : Section1.ClassFunction L} (z : ℤ) :
    integerSpan S φ → integerSpan S ((z : ℂ) • φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨z • v, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.mul_sum, mul_assoc]

/-- Linear maps commute with integral coefficient evaluation. -/
public theorem map_evalCoeff
    {L : Type u} [Group L]
    {G : Type u} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (μ : ι → Section1.ClassFunction L)
    (v : Section1.CoeffVector ι) :
    T (Section1.evalCoeff μ v) = Section1.evalCoeff (fun i => T (μ i)) v := by
  classical
  ext g
  simp [Section1.evalCoeff, Finset.sum_apply]

/-- Integral coefficient evaluation preserves equality of Gram matrices. -/
public theorem scalarProduct_evalCoeff_eq_of_gram_eq
    {L : Type u} [Group L] [Finite L]
    {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Fintype ι]
    (μ : ι → Section1.ClassFunction L)
    (ν : ι → Section1.ClassFunction G)
    (hgram : ∀ i j, Section1.scalarProduct G (ν i) (ν j) =
      Section1.scalarProduct L (μ i) (μ j))
    (v w : Section1.CoeffVector ι) :
    Section1.scalarProduct G (Section1.evalCoeff ν v) (Section1.evalCoeff ν w) =
      Section1.scalarProduct L (Section1.evalCoeff μ v) (Section1.evalCoeff μ w) := by
  have hleftG :
      (∑ i : ι, (v i : ℂ) • ν i) =
        (fun g : G => ∑ i : ι, ((v i : ℂ) • ν i) g) := by
    ext g
    simp
  have hrightG :
      (∑ i : ι, (w i : ℂ) • ν i) =
        (fun g : G => ∑ i : ι, ((w i : ℂ) • ν i) g) := by
    ext g
    simp
  have hleftL :
      (∑ i : ι, (v i : ℂ) • μ i) =
        (fun g : L => ∑ i : ι, ((v i : ℂ) • μ i) g) := by
    ext g
    simp
  have hrightL :
      (∑ i : ι, (w i : ℂ) • μ i) =
        (fun g : L => ∑ i : ι, ((w i : ℂ) • μ i) g) := by
    ext g
    simp
  calc
    Section1.scalarProduct G (Section1.evalCoeff ν v) (Section1.evalCoeff ν w) =
        ∑ i : ι, ∑ j : ι,
          (v i : ℂ) * (star (w j : ℂ) * Section1.scalarProduct G (ν i) (ν j)) := by
            simp only [Section1.evalCoeff]
            rw [hleftG, hrightG, Section1.scalarProduct_fintype_sum_left]
            simp_rw [Section1.scalarProduct_smul_left]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_fintype_sum_right]
            simp_rw [Section1.scalarProduct_smul_right]
            rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ j : ι,
          (v i : ℂ) * (star (w j : ℂ) * Section1.scalarProduct L (μ i) (μ j)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [hgram i j]
    _ = Section1.scalarProduct L (Section1.evalCoeff μ v) (Section1.evalCoeff μ w) := by
          symm
          simp only [Section1.evalCoeff]
          rw [hleftL, hrightL, Section1.scalarProduct_fintype_sum_left]
          simp_rw [Section1.scalarProduct_smul_left]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Section1.scalarProduct_fintype_sum_right]
          simp_rw [Section1.scalarProduct_smul_right]
          rw [Finset.mul_sum]

/--
`χ ∈ Z[S, A]`: the class function `χ` is an integral linear combination of
`S` and is supported on `A`.
-/
@[expose] public def integerSpanOn
    {L : Type u} [Group L]
    (S : Finset (Section1.ClassFunction L))
    (A : Set L)
    (χ : Section1.ClassFunction L) : Prop :=
  integerSpan S χ ∧ Section1.supportedOn χ A


public theorem supportedOn_add
    {L : Type u} [Group L]
    {A : Set L}
    {φ ψ : Section1.ClassFunction L}
    (hφ : Section1.supportedOn φ A)
    (hψ : Section1.supportedOn ψ A) :
    Section1.supportedOn (φ + ψ) A := by
  rw [Section1.supportedOn_iff] at hφ hψ ⊢
  intro g hg
  simp [hφ g hg, hψ g hg]

public theorem supportedOn_smul
    {L : Type u} [Group L]
    {A : Set L}
    {φ : Section1.ClassFunction L}
    (z : ℂ)
    (hφ : Section1.supportedOn φ A) :
    Section1.supportedOn (z • φ) A := by
  rw [Section1.supportedOn_iff] at hφ ⊢
  intro g hg
  simp [hφ g hg]

public theorem supportedOn_neg
    {L : Type u} [Group L]
    {A : Set L}
    {φ : Section1.ClassFunction L}
    (hφ : Section1.supportedOn φ A) :
    Section1.supportedOn (-φ) A := by
  simpa using supportedOn_smul (-1 : ℂ) hφ

public theorem supportedOn_sub
    {L : Type u} [Group L]
    {A : Set L}
    {φ ψ : Section1.ClassFunction L}
    (hφ : Section1.supportedOn φ A)
    (hψ : Section1.supportedOn ψ A) :
    Section1.supportedOn (φ - ψ) A := by
  simpa [sub_eq_add_neg] using supportedOn_add hφ (supportedOn_neg hψ)

public theorem supportedOn_puncturedSet_iff_degree_eq_zero
    {L : Type u} [Group L]
    (φ : Section1.ClassFunction L) :
    Section1.supportedOn φ puncturedSet ↔ Section1.degree φ = 0 := by
  constructor
  · intro hφ
    rw [Section1.degree_apply]
    exact (Section1.supportedOn_iff.mp hφ) 1 (by simp [puncturedSet])
  · intro hdeg
    rw [Section1.supportedOn_iff]
    intro g hg
    have hg1 : g = 1 := by simpa [puncturedSet] using hg
    rw [hg1]
    simpa [Section1.degree_apply] using hdeg


public theorem integerSpanOn_mono
    {L : Type u} [Group L]
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    (hsub : S₁ ⊆ S₂)
    {A : Set L}
    {χ : Section1.ClassFunction L} :
    integerSpanOn S₁ A χ → integerSpanOn S₂ A χ := by
  rintro ⟨hχ, hχA⟩
  exact ⟨integerSpan_mono hsub hχ, hχA⟩

public theorem degree_conjugateCharacter_eq_of_isCharacter
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsCharacter χ) :
    Section1.degree (Section1.conjugateCharacter χ) = Section1.degree χ := by
  rcases hχ with ⟨V, _hadd, _hmod, _hfd, ρ, rfl⟩
  calc
    Section1.degree (Section1.conjugateCharacter ρ.character) =
        star (Section1.degree ρ.character) := by
      simp [Section1.degree, Section1.conjugateCharacter]
    _ = Section1.degree ρ.character := by
      rw [Section1.degree_representation_character ρ]
      simp

/-- The book condition `Z[S, A] ≠ 0`. -/
@[expose] public def integerSpanOnNonempty
    {L : Type u} [Group L]
    (S : Finset (Section1.ClassFunction L))
    (A : Set L) : Prop :=
  ∃ χ : Section1.ClassFunction L, integerSpanOn S A χ ∧ χ ≠ 0

public theorem integerSpanOnNonempty_of_conjugate_pair
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ S)
    (hχbar : Section1.conjugateCharacter χ ∈ S)
    (hχne : χ ≠ Section1.conjugateCharacter χ)
    (hχchar : Section1.IsCharacter χ) :
    integerSpanOnNonempty S puncturedSet := by
  refine ⟨χ - Section1.conjugateCharacter χ, ?_, ?_⟩
  · refine ⟨integerSpan_sub (integerSpan_of_mem S hχ)
      (integerSpan_of_mem S hχbar), ?_⟩
    apply (supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree χ - Section1.degree (Section1.conjugateCharacter χ) = 0
    rw [degree_conjugateCharacter_eq_of_isCharacter hχchar]
    simp
  · intro hzero
    apply hχne
    have h := congrArg (fun f : Section1.ClassFunction L =>
      f + Section1.conjugateCharacter χ) hzero
    ext g
    have hg := congrFun h g
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hg

/-- The source condition `S ⊂ Z[Irr L]`. -/
@[expose] public def sourceVirtualCharacters
    {L : Type u} [Group L]
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  ∀ χ : Section1.ClassFunction L, χ ∈ S → Theory.Character.IsVirtualCharacter χ

public theorem sourceVirtualCharacters_mono
    {L : Type u} [Group L]
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    (hsub : S₁ ⊆ S₂) :
    sourceVirtualCharacters S₂ → sourceVirtualCharacters S₁ := by
  intro hsrc χ hχ
  exact hsrc χ (hsub hχ)

public theorem isVirtualCharacter_of_isCharacter
    {L : Type u} [Group L] [Finite L] {χ : Section1.ClassFunction L}
    (hχ : Section1.IsCharacter χ) :
    Theory.Character.IsVirtualCharacter χ := by
  classical
  rcases hχ with ⟨V, _add, _module, _finiteDimensional, ρ, rfl⟩
  refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)),
    (fun _ : Fin 1 => Module.finrank ℂ V),
    (fun _ : Fin 1 => Section1.standardizeRepresentation ρ), ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations,
    Section1.standardizeRepresentation_character]

/-- Pairwise orthogonality for the finite family `S`. -/
@[expose] public def orthogonalFinset
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  ∀ ⦃χ ψ : Section1.ClassFunction L⦄,
    χ ∈ S → ψ ∈ S → χ ≠ ψ → Section1.scalarProduct L χ ψ = 0

/-- Every member of `R` is orthogonal to every member of `S`. -/
@[expose] public def orthogonalFinsets
    {G : Type u} [Group G] [Finite G]
    (R S : Finset (Section1.ClassFunction G)) : Prop :=
  ∀ ⦃φ ψ : Section1.ClassFunction G⦄,
    φ ∈ R → ψ ∈ S → Section1.scalarProduct G φ ψ = 0

/-- A single class function is orthogonal to every member of `R`. -/
@[expose] public def orthogonalToFinset
    {G : Type u} [Group G] [Finite G]
    (R : Finset (Section1.ClassFunction G))
    (φ : Section1.ClassFunction G) : Prop :=
  ∀ ⦃ψ : Section1.ClassFunction G⦄,
    ψ ∈ R → Section1.scalarProduct G φ ψ = 0

/--
The Hermitian square norm `‖φ‖²`, recorded as the real part of the
self-scalar-product.
-/
@[expose] public def cfNormSq
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) : ℝ :=
  Complex.re (Section1.scalarProduct G φ φ)

public theorem cfNormSq_eq_inv_card_mul_sum_normSq
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    cfNormSq φ = (Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (φ g) := by
  unfold cfNormSq Section1.scalarProduct
  have hcast : ((Nat.card G : ℂ)⁻¹) = (((Nat.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  calc
    Complex.re (φ g * star (φ g)) = Complex.re (star (φ g) * φ g) := by
      rw [mul_comm]
    _ = Complex.re ((Complex.normSq (φ g) : ℝ) : ℂ) := by
      congr 1
      simpa using (Complex.normSq_eq_conj_mul_self (z := φ g)).symm
    _ = Complex.normSq (φ g) := by
      simp

public theorem cfNormSq_nonneg
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    0 ≤ cfNormSq φ := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun g _hg => Complex.normSq_nonneg (φ g)))

public theorem cfNormSq_eq_zero
    {G : Type u} [Group G] [Finite G]
    {φ : Section1.ClassFunction G}
    (hφ : cfNormSq φ = 0) :
    φ = 0 := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq] at hφ
  have hcardNat : 0 < Nat.card G := Nat.card_pos
  have hcardReal : 0 < (Nat.card G : ℝ) := by
    exact_mod_cast hcardNat
  have hcard : 0 < (Nat.card G : ℝ)⁻¹ := inv_pos.mpr hcardReal
  have hsumZero : (∑ g : G, Complex.normSq (φ g)) = 0 := by
    nlinarith
  have hzeroAll : ∀ g ∈ (Finset.univ : Finset G), Complex.normSq (φ g) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun g _hg => Complex.normSq_nonneg (φ g))).1 hsumZero
  ext g
  exact Complex.normSq_eq_zero.mp (hzeroAll g (by simp))

public theorem scalarProduct_self_eq_cfNormSq_of_character
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsCharacter χ) :
    Section1.scalarProduct G χ χ = (cfNormSq χ : ℂ) := by
  rcases Section1.scalarProduct_character_character_eq_nat χ χ hχ hχ with ⟨n, hn⟩
  have hnorm : cfNormSq χ = (n : ℝ) := by
    unfold cfNormSq
    rw [hn]
    simp
  calc
    Section1.scalarProduct G χ χ = (n : ℂ) := hn
    _ = (cfNormSq χ : ℂ) := by simp [hnorm]

/-- The self scalar product of any class function is the complex coercion of
its real square norm. -/
public theorem scalarProduct_self_eq_cfNormSq
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ φ = (cfNormSq φ : ℂ) := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq]
  unfold Section1.scalarProduct
  have hcard :
      ((Nat.card G : ℂ)⁻¹) = (((Nat.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  have hsum :
      (∑ g : G, φ g * star (φ g)) =
        ((∑ g : G, Complex.normSq (φ g) : ℝ) : ℂ) := by
    calc
      (∑ g : G, φ g * star (φ g)) =
          ∑ g : G, ((Complex.normSq (φ g) : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro g _hg
        calc
          φ g * star (φ g) = star (φ g) * φ g := by rw [mul_comm]
          _ = ((Complex.normSq (φ g) : ℝ) : ℂ) := by
            simpa using (Complex.normSq_eq_conj_mul_self (z := φ g)).symm
      _ = ((∑ g : G, Complex.normSq (φ g) : ℝ) : ℂ) := by
        norm_cast
  rw [hcard, hsum, Complex.ofReal_mul]

public theorem scalarProduct_add_right
    {G : Type*} [Finite G]
    (φ ψ₁ ψ₂ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ₁ + ψ₂) =
      Section1.scalarProduct G φ ψ₁ + Section1.scalarProduct G φ ψ₂ := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

public theorem scalarProduct_sub_left
    {G : Type*} [Finite G]
    (φ₁ φ₂ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (φ₁ - φ₂) ψ =
      Section1.scalarProduct G φ₁ ψ - Section1.scalarProduct G φ₂ ψ := by
  rw [sub_eq_add_neg, Section1.scalarProduct_add_left]
  rw [show -φ₂ = (-1 : ℂ) • φ₂ by ext g; simp]
  rw [Section1.scalarProduct_smul_left]
  ring

public theorem scalarProduct_sub_right
    {G : Type*} [Finite G]
    (φ ψ₁ ψ₂ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ₁ - ψ₂) =
      Section1.scalarProduct G φ ψ₁ - Section1.scalarProduct G φ ψ₂ := by
  rw [sub_eq_add_neg, scalarProduct_add_right]
  rw [show -ψ₂ = (-1 : ℂ) • ψ₂ by ext g; simp]
  rw [Section1.scalarProduct_smul_right]
  simp [sub_eq_add_neg]

public theorem cfNormSq_add_eq_add_of_orthogonal
    {G : Type*} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G}
    (hφψ : Section1.scalarProduct G φ ψ = 0)
    (hψφ : Section1.scalarProduct G ψ φ = 0) :
    cfNormSq (φ + ψ) = cfNormSq φ + cfNormSq ψ := by
  unfold cfNormSq
  rw [Section1.scalarProduct_add_left, scalarProduct_add_right,
    scalarProduct_add_right]
  rw [hφψ, hψφ]
  norm_num

public theorem cfNormSq_sub_eq_add_of_orthogonal
    {G : Type*} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G}
    (hφψ : Section1.scalarProduct G φ ψ = 0)
    (hψφ : Section1.scalarProduct G ψ φ = 0) :
    cfNormSq (φ - ψ) = cfNormSq φ + cfNormSq ψ := by
  unfold cfNormSq
  rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
  rw [hφψ, hψφ]
  norm_num

public theorem cfNormSq_smul
    {G : Type*} [Group G] [Finite G]
    (z : ℂ) (φ : Section1.ClassFunction G) :
    cfNormSq (z • φ) = Complex.normSq z * cfNormSq φ := by
  unfold cfNormSq
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
  have hnorm : z * star z = (Complex.normSq z : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp [mul_comm]
  rw [← mul_assoc, hnorm]
  simp

/-- `φ` is a sum of a subset of the finite family `R`. -/
@[expose] public def isSubsetSumOf
    {G : Type u} [Group G]
    (R : Finset (Section1.ClassFunction G))
    (φ : Section1.ClassFunction G) : Prop :=
  ∃ E : Finset (Section1.ClassFunction G), E ⊆ R ∧ φ = Finset.sum E fun ψ => ψ


/-- `T` preserves the inner product on the lattice `Z[S]`. -/
@[expose] public def isCFLinearIsometryOnSpan
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ φ ψ : Section1.ClassFunction L,
    integerSpan S φ → integerSpan S ψ →
      Section1.scalarProduct G (T φ) (T ψ) = Section1.scalarProduct L φ ψ

public theorem isCFLinearIsometryOnSpan_apply_of_mem
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hT : isCFLinearIsometryOnSpan S T)
    {φ ψ : Section1.ClassFunction L}
    (hφ : φ ∈ S) (hψ : ψ ∈ S) :
    Section1.scalarProduct G (T φ) (T ψ) =
    Section1.scalarProduct L φ ψ :=
  hT φ ψ (integerSpan_of_mem S hφ) (integerSpan_of_mem S hψ)

public theorem isCFLinearIsometryOnSpan_mono
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    (hsub : S₁ ⊆ S₂)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    isCFLinearIsometryOnSpan S₂ T → isCFLinearIsometryOnSpan S₁ T := by
  intro hIso φ ψ hφ hψ
  exact hIso φ ψ (integerSpan_mono hsub hφ) (integerSpan_mono hsub hψ)

/-- `T` preserves the inner product on the lattice `Z[S, A]`. -/
@[expose] public def isCFLinearIsometryOnSpanOn
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (A : Set L)
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ φ ψ : Section1.ClassFunction L,
    integerSpanOn S A φ → integerSpanOn S A ψ →
      Section1.scalarProduct G (T φ) (T ψ) = Section1.scalarProduct L φ ψ

/--
An orthonormal finite family of signed irreducible characters, recorded as a
finite set.
-/
@[expose] public def signedOrthonormalFinset
    {G : Type u} [Group G] [Finite G]
    (R : Finset (Section1.ClassFunction G)) : Prop :=
  (∀ φ : Section1.ClassFunction G, φ ∈ R → Section3.IsSignedIrreducibleCharacter φ) ∧
    orthogonalFinset R

/-- `T` sends every element of `Z[S]` to a virtual character of `G`. -/
@[expose] public def mapsIntegerSpanToVirtualCharacters
    {L : Type u} [Group L]
    {G : Type u} [Group G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ χ : Section1.ClassFunction L,
    integerSpan S χ → Theory.Character.IsVirtualCharacter (T χ)

public theorem mapsIntegerSpanToVirtualCharacters_mono
    {L : Type u} [Group L]
    {G : Type u} [Group G]
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    (hsub : S₁ ⊆ S₂)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    mapsIntegerSpanToVirtualCharacters S₂ T →
      mapsIntegerSpanToVirtualCharacters S₁ T := by
  intro hvirt χ hχ
  exact hvirt χ (integerSpan_mono hsub hχ)

/-- `T'` agrees with `T` on the lattice `Z[S, A]`. -/
@[expose] public def agreesOnIntegerSpanOn
    {L : Type u} [Group L]
    {G : Type u} [Group G]
    (S : Finset (Section1.ClassFunction L))
    (A : Set L)
    (T T' : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ χ : Section1.ClassFunction L,
    integerSpanOn S A χ → T' χ = T χ

public theorem agreesOnIntegerSpanOn_mono
    {L : Type u} [Group L]
    {G : Type u} [Group G]
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    (hsub : S₁ ⊆ S₂)
    {A : Set L}
    {T T' : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    agreesOnIntegerSpanOn S₂ A T T' → agreesOnIntegerSpanOn S₁ A T T' := by
  intro hagree χ hχ
  exact hagree χ (integerSpanOn_mono hsub hχ)

/--
Peterfalvi Definition `(5.1)`: `S` lies in `Z[Irr L]`, `Z[S, A]` is nonzero,
and `T` extends from `Z[S, A]` to an isometry on `Z[S]` with values in virtual
characters.
-/
@[expose] public def IsCoherentTriple
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (A : Set L)
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  sourceVirtualCharacters S ∧
    integerSpanOnNonempty S A ∧
      ∃ T' : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
        isCFLinearIsometryOnSpan S T' ∧
          mapsIntegerSpanToVirtualCharacters S T' ∧
            agreesOnIntegerSpanOn S A T T'

public theorem IsCoherentTriple_mono
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {A : Set L}
    {S₁ S₂ : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hsub : S₁ ⊆ S₂)
    (hnonempty : integerSpanOnNonempty S₁ A) :
    IsCoherentTriple A S₂ T → IsCoherentTriple A S₁ T := by
  rintro ⟨hsrc, _hS₂nonempty, T', hIso, hvirt, hagree⟩
  exact ⟨sourceVirtualCharacters_mono hsub hsrc, hnonempty, T',
    isCFLinearIsometryOnSpan_mono hsub hIso,
    mapsIntegerSpanToVirtualCharacters_mono hsub hvirt,
    agreesOnIntegerSpanOn_mono hsub hagree⟩

end CFSG.Section5

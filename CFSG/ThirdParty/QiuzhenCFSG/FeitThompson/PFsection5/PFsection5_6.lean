module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_2

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 5, Theorem (5.6)

This file isolates PF `(5.6)` as its own proof target.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section5

universe v
universe u

/-! ## (5.6) -/

/--
Peterfalvi `(5.6)`: under Hypothesis `(5.2)`, if `S₁ ⊆ S` is closed under
complex conjugation and already coherent, and if `X₁ ∈ S₁` and `X ∈ S`
satisfy the degree divisibility and degree/norm inequality from the source,
then adjoining `{X, X̄}` preserves coherence.

The numeric hypothesis `(c)` is packaged with explicit natural-number degree
data on `S₁`, `X₁`, and `X`.
-/
@[expose] public def theorem_5_6_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ R : S → Finset (Section1.ClassFunction G),
    hypothesis_5_2_setup_statement S →
      hypothesis_5_2_a_statement S →
        hypothesis_5_2_b_statement S T →
          hypothesis_5_2_c_statement S →
            hypothesis_5_2_d_statement S T R →
              hypothesis_5_2_e_statement S R →
                ∀ S1 : Finset (Section1.ClassFunction L),
                  S1 ⊆ S →
                    (∀ χ : Section1.ClassFunction L,
                      χ ∈ S1 →
                        Section1.conjugateCharacter χ ∈ S1) →
                      ∀ X : S,
                        Section1.conjugateCharacter
                            (X : Section1.ClassFunction L) ∉ S1 →
                          ∀ X1 : S1,
                            definition_5_1_statement puncturedSet S1 T →
                              (∃ d1 dX : ℕ,
                                Section1.degree (X1 : Section1.ClassFunction L) = (d1 : ℂ) ∧
                                  Section1.degree (X : Section1.ClassFunction L) = (dX : ℂ) ∧
                                    d1 ∣ dX ∧
                                      ∃ dS1 : S1 → ℕ,
                                        (∀ Y : S1,
                                          Section1.degree (Y : Section1.ClassFunction L) =
                                            (dS1 Y : ℂ)) ∧
                                          2 * (dX : ℝ) * (d1 : ℝ) <
                                            ∑ Y : S1,
                                              (((dS1 Y : ℝ) ^ (2 : ℕ)) /
                                                cfNormSq (Y : Section1.ClassFunction L))) →
                                definition_5_1_statement puncturedSet
                                  (S1 ∪
                                    ({(X : Section1.ClassFunction L),
                                      Section1.conjugateCharacter
                                        (X : Section1.ClassFunction L)} :
                                      Finset (Section1.ClassFunction L)))
                                  T


private theorem integerSpan_of_mem_pf56
    {H : Type*} [Group H] [Finite H]
    (S : Finset (Section1.ClassFunction H))
    {χ : Section1.ClassFunction H}
    (hχ : χ ∈ S) :
    integerSpan S χ := by
  classical
  refine ⟨Section1.basisVector ⟨χ, hχ⟩, ?_⟩
  ext g
  rw [Section1.evalCoeff, Finset.sum_eq_single ⟨χ, hχ⟩]
  · simp [Section1.basisVector]
  · intro x _hx hxne
    simp [Section1.basisVector, hxne]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private theorem integerSpan_mono_pf56
    {H : Type*} [Group H]
    {S1 S2 : Finset (Section1.ClassFunction H)}
    (hsub : S1 ⊆ S2)
    {χ : Section1.ClassFunction H} :
    integerSpan S1 χ → integerSpan S2 χ := by
  classical
  rintro ⟨v, rfl⟩
  let w : Section1.CoeffVector S2 := fun y =>
    if hy : (y : Section1.ClassFunction H) ∈ S1 then v ⟨y, hy⟩ else 0
  refine ⟨w, ?_⟩
  ext g
  have hsum := Finset.sum_subset
      (s₁ := S1) (s₂ := S2)
      (f := fun y : Section1.ClassFunction H =>
        (((if hy : y ∈ S1 then v ⟨y, hy⟩ else 0 : Int) : ℂ) * y g))
      hsub
      (by
        intro y hyS2 hyS1
        simp [hyS1])
  simpa +contextual [Section1.evalCoeff, w, smul_eq_mul, ← S1.sum_attach, ← S2.sum_attach] using
    hsum

private theorem integerSpan_add_pf56
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ + ψ) := by
  classical
  rintro ⟨v, rfl⟩ ⟨w, rfl⟩
  refine ⟨v + w, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.sum_add_distrib, add_mul]

private theorem integerSpan_nsmul_pf56
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H} (n : ℕ) :
    integerSpan S φ → integerSpan S ((n : ℂ) • φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨n • v, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.mul_sum, mul_assoc]

private theorem integerSpan_neg_pf56
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H} :
    integerSpan S φ → integerSpan S (-φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  ext g
  simp [Section1.evalCoeff]

private theorem integerSpan_sub_pf56
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ - ψ) := by
  intro hφ hψ
  simpa [sub_eq_add_neg] using integerSpan_add_pf56 hφ (integerSpan_neg_pf56 hψ)

private theorem integerSpan_zsmul_pf56
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H} (z : Int) :
    integerSpan S φ → integerSpan S ((z : ℂ) • φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨z • v, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.mul_sum, mul_assoc]

private theorem supportedOn_zero_pf56
    {H : Type*} [Group H]
    {A : Set H} :
    Section1.supportedOn (0 : Section1.ClassFunction H) A := by
  rw [Section1.supportedOn_iff]
  intro g hg
  simp

private theorem supportedOn_add_pf56
    {H : Type*} [Group H]
    {A : Set H}
    {φ ψ : Section1.ClassFunction H}
    (hφ : Section1.supportedOn φ A)
    (hψ : Section1.supportedOn ψ A) :
    Section1.supportedOn (φ + ψ) A := by
  rw [Section1.supportedOn_iff] at hφ hψ ⊢
  intro g hg
  simp [hφ g hg, hψ g hg]

private theorem supportedOn_smul_pf56
    {H : Type*} [Group H]
    {A : Set H}
    {φ : Section1.ClassFunction H}
    (z : ℂ)
    (hφ : Section1.supportedOn φ A) :
    Section1.supportedOn (z • φ) A := by
  rw [Section1.supportedOn_iff] at hφ ⊢
  intro g hg
  simp [hφ g hg]

private theorem integerSpanOn_add_pf56
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {A : Set H}
    {φ ψ : Section1.ClassFunction H} :
    integerSpanOn S A φ → integerSpanOn S A ψ → integerSpanOn S A (φ + ψ) := by
  rintro ⟨hφ_span, hφ_on⟩ ⟨hψ_span, hψ_on⟩
  exact ⟨integerSpan_add_pf56 hφ_span hψ_span, supportedOn_add_pf56 hφ_on hψ_on⟩


private theorem integerSpanOn_zsmul_pf56
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {A : Set H}
    {φ : Section1.ClassFunction H} (z : Int) :
    integerSpanOn S A φ → integerSpanOn S A ((z : ℂ) • φ) := by
  rintro ⟨hφ_span, hφ_on⟩
  exact ⟨integerSpan_zsmul_pf56 z hφ_span, supportedOn_smul_pf56 (z : ℂ) hφ_on⟩

private theorem integerSpanOn_sum_pf56
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {A : Set H}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction H)
    (hμ : ∀ i, integerSpanOn S A (μ i))
    (v : Section1.CoeffVector ι) :
    integerSpanOn S A (Section1.evalCoeff μ v) := by
  classical
  rw [Section1.evalCoeff]
  let f : ι → Section1.ClassFunction H := fun i => ((v i : ℂ) • μ i)
  have hf : ∀ i, integerSpanOn S A (f i) := by
    intro i
    dsimp [f]
    exact integerSpanOn_zsmul_pf56 (v i) (hμ i)
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa [f] using
        (show integerSpanOn S A (0 : Section1.ClassFunction H) from
          ⟨⟨0, by simp [Section1.evalCoeff]⟩, supportedOn_zero_pf56⟩)
  | @insert i t hit ih =>
      have ht : integerSpanOn S A (Finset.sum t f) := by
        simpa [f] using ih
      have hi : integerSpanOn S A (f i) := hf i
      simpa [f, Finset.sum_insert hit] using integerSpanOn_add_pf56 hi ht

private theorem integerSpanOn_of_generators_pf56
    {H : Type*} [Group H]
    {S U : Finset (Section1.ClassFunction H)}
    {A : Set H}
    {φ : Section1.ClassFunction H}
    (hU : ∀ ψ : Section1.ClassFunction H, ψ ∈ U → integerSpanOn S A ψ) :
    integerSpan U φ → integerSpanOn S A φ := by
  classical
  rintro ⟨v, rfl⟩
  exact integerSpanOn_sum_pf56
    (μ := fun ψ : U => (ψ : Section1.ClassFunction H))
    (hμ := fun ψ => hU ψ ψ.2)
    v

private theorem isCFLinearIsometryOnSpan_mono_pf56
    {L G : Type u} [Group L] [Finite L] [Group G] [Finite G]
    {S1 S2 : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S2)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    isCFLinearIsometryOnSpan S2 T → isCFLinearIsometryOnSpan S1 T := by
  intro hIso φ ψ hφ hψ
  exact hIso φ ψ (integerSpan_mono_pf56 hsub hφ) (integerSpan_mono_pf56 hsub hψ)

private theorem mapsIntegerSpanToVirtualCharacters_mono_pf56
    {L G : Type u} [Group L] [Group G]
    {S1 S2 : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S2)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    mapsIntegerSpanToVirtualCharacters S2 T →
      mapsIntegerSpanToVirtualCharacters S1 T := by
  intro hvirt χ hχ
  exact hvirt χ (integerSpan_mono_pf56 hsub hχ)

private theorem supportedOn_puncturedSet_iff_degree_eq_zero_pf56
    {H : Type*} [Group H]
    (φ : Section1.ClassFunction H) :
    Section1.supportedOn φ puncturedSet ↔ Section1.degree φ = 0 := by
  constructor
  · intro hSupp
    rw [Section1.degree_apply]
    exact (Section1.supportedOn_iff.mp hSupp) 1 (by simp [puncturedSet])
  · intro hdeg
    rw [Section1.supportedOn_iff]
    intro g hg
    have hg1 : g = 1 := by
      by_contra hne
      exact hg (by simp [puncturedSet, hne])
    subst hg1
    simpa [Section1.degree_apply] using hdeg

private theorem orthogonalToFinset_of_subsetSum_of_orthogonalFinsets_pf56
    {H : Type*} [Group H] [Finite H]
    {R1 R2 : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H}
    (hsubset : isSubsetSumOf R1 φ)
    (horth : orthogonalFinsets R1 R2) :
    orthogonalToFinset R2 φ := by
  rcases hsubset with ⟨E, hE, rfl⟩
  intro ψ hψ
  induction E using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert χ E hχE ih =>
      have hE' : E ⊆ R1 := by
        intro ξ hξ
        exact hE (by simp [hξ])
      rw [Finset.sum_insert hχE, Section1.scalarProduct_add_left, ih hE']
      simpa using horth (hE (Finset.mem_insert_self χ E)) hψ

private theorem scalarProduct_zero_swap_pf56
    {H : Type*} [Finite H]
    {φ ψ : Section1.ClassFunction H}
    (h : Section1.scalarProduct H φ ψ = 0) :
    Section1.scalarProduct H ψ φ = 0 := by
  simpa [Section1.scalarProduct_star_swap] using congrArg star h

private theorem scalarProduct_add_right_pf56
    {H : Type*} [Finite H]
    (φ ψ1 ψ2 : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ1 + ψ2) =
      Section1.scalarProduct H φ ψ1 + Section1.scalarProduct H φ ψ2 := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_sub_right_pf56
    {H : Type*} [Finite H]
    (φ ψ1 ψ2 : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ1 - ψ2) =
      Section1.scalarProduct H φ ψ1 - Section1.scalarProduct H φ ψ2 := by
  calc
    Section1.scalarProduct H φ (ψ1 - ψ2)
        = Section1.scalarProduct H φ (ψ1 + (-1 : ℂ) • ψ2) := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H φ ψ1 +
          Section1.scalarProduct H φ ((-1 : ℂ) • ψ2) := by
            rw [scalarProduct_add_right_pf56]
    _ = Section1.scalarProduct H φ ψ1 - Section1.scalarProduct H φ ψ2 := by
          rw [Section1.scalarProduct_smul_right]
          simp [sub_eq_add_neg]

private theorem scalarProduct_sub_left_pf56
    {H : Type*} [Finite H]
    (φ1 φ2 ψ : Section1.ClassFunction H) :
    Section1.scalarProduct H (φ1 - φ2) ψ =
      Section1.scalarProduct H φ1 ψ - Section1.scalarProduct H φ2 ψ := by
  calc
    Section1.scalarProduct H (φ1 - φ2) ψ
        = Section1.scalarProduct H (φ1 + (-1 : ℂ) • φ2) ψ := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H φ1 ψ +
          Section1.scalarProduct H ((-1 : ℂ) • φ2) ψ := by
            rw [Section1.scalarProduct_add_left]
    _ = Section1.scalarProduct H φ1 ψ - Section1.scalarProduct H φ2 ψ := by
          rw [Section1.scalarProduct_smul_left]
          simp [sub_eq_add_neg]

private theorem scalarProduct_self_of_irreducibleCharacterOnGroup_pf56
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  simpa using Section1.scalarProduct_representation_char_self ρ hρ

private theorem scalarProduct_self_of_signedIrreducible_pf56
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμself : Section1.scalarProduct G μ μ = 1 :=
    scalarProduct_self_of_irreducibleCharacterOnGroup_pf56 hμ
  rcases hε with rfl | rfl
  · simp [hμself]
  · calc
      Section1.scalarProduct G ((-1 : ℂ) • μ) ((-1 : ℂ) • μ)
          = (-1 : ℂ) * (star (-1 : ℂ)) * Section1.scalarProduct G μ μ := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
              ring
      _ = 1 := by simp [hμself]

private theorem scalarProduct_eq_ite_of_signedOrthonormalFinset_pf56
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R) :
    ∀ a b : R, Section1.scalarProduct G (a : Section1.ClassFunction G) b =
      if a = b then 1 else 0 := by
  intro a b
  by_cases hab : a = b
  · subst hab
    simpa using scalarProduct_self_of_signedIrreducible_pf56 (hR.1 _ a.2)
  · simpa [hab] using hR.2 a.2 b.2 (fun hEq => hab (Subtype.ext hEq))

private theorem scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf56
    {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G)
    (horth : ∀ i j, Section1.scalarProduct G (μ i) (μ j) = if i = j then 1 else 0)
    (v w : Section1.CoeffVector ι) :
    Section1.scalarProduct G (Section1.evalCoeff μ v) (Section1.evalCoeff μ w) =
      (Section1.coeffDot v w : ℂ) := by
  classical
  have hleft :
      (∑ j : ι, (v j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((v j : ℂ) • μ j) g) := by
    ext g
    simp
  have hright :
      (∑ j : ι, (w j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((w j : ℂ) • μ j) g) := by
    ext g
    simp
  simp only [Section1.evalCoeff]
  rw [hleft, hright]
  rw [Section1.scalarProduct_fintype_sum_left]
  simp_rw [Section1.scalarProduct_smul_left]
  change ∑ i : ι, (v i : ℂ) *
      Section1.scalarProduct G (μ i) (fun g : G => ∑ j : ι, ((w j : ℂ) • μ j) g) =
    ((∑ i : ι, v i * w i : ℤ) : ℂ)
  rw [show ((∑ i : ι, v i * w i : ℤ) : ℂ) =
      ∑ i : ι, ((v i * w i : ℤ) : ℂ) by simp]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Section1.scalarProduct_fintype_sum_right]
  simp_rw [Section1.scalarProduct_smul_right]
  calc
    (v i : ℂ) * (∑ x : ι, star (w x : ℂ) * Section1.scalarProduct G (μ i) (μ x)) =
        (v i : ℂ) * (w i : ℂ) := by
          simp [horth]
    _ = (v i * w i : ℤ) := by
          simp [Int.cast_mul]

private theorem orthogonalToFinset_scalarProduct_evalCoeff_zero_pf56
    {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G)
    {Y : Section1.ClassFunction G}
    (hY : ∀ i, Section1.scalarProduct G Y (μ i) = 0)
    (v : Section1.CoeffVector ι) :
    Section1.scalarProduct G Y (Section1.evalCoeff μ v) = 0 := by
  have hright :
      (∑ j : ι, (v j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((v j : ℂ) • μ j) g) := by
    ext g
    simp
  rw [Section1.evalCoeff, hright, Section1.scalarProduct_fintype_sum_right]
  simp_rw [Section1.scalarProduct_smul_right, hY]
  simp

private theorem cfNormSq_sub_eq_add_of_orthogonal_pf56
    {H : Type*} [Group H] [Finite H]
    {φ ψ : Section1.ClassFunction H}
    (hφψ : Section1.scalarProduct H φ ψ = 0)
    (hψφ : Section1.scalarProduct H ψ φ = 0) :
    cfNormSq (φ - ψ) = cfNormSq φ + cfNormSq ψ := by
  unfold cfNormSq
  rw [scalarProduct_sub_left_pf56, scalarProduct_sub_right_pf56, scalarProduct_sub_right_pf56]
  simp [hφψ, hψφ]

private theorem cfNormSq_add_eq_add_of_orthogonal_pf56
    {H : Type*} [Group H] [Finite H]
    {φ ψ : Section1.ClassFunction H}
    (hφψ : Section1.scalarProduct H φ ψ = 0)
    (hψφ : Section1.scalarProduct H ψ φ = 0) :
    cfNormSq (φ + ψ) = cfNormSq φ + cfNormSq ψ := by
  unfold cfNormSq
  rw [Section1.scalarProduct_add_left, scalarProduct_add_right_pf56,
    scalarProduct_add_right_pf56]
  simp [hφψ, hψφ]

private theorem cfNormSq_eq_inv_card_mul_sum_normSq_pf56
    {H : Type*} [Group H] [Finite H]
    (φ : Section1.ClassFunction H) :
    cfNormSq φ = (Nat.card H : ℝ)⁻¹ * ∑ g : H, Complex.normSq (φ g) := by
  unfold cfNormSq Section1.scalarProduct
  have hcast :
      ((Nat.card H : ℂ)⁻¹) = (((Nat.card H : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  calc
    Complex.re (φ g * star (φ g))
      = Complex.re (star (φ g) * φ g) := by rw [mul_comm]
    _ = Complex.re ((Complex.normSq (φ g) : ℝ) : ℂ) := by
          congr 1
          simpa using (Complex.normSq_eq_conj_mul_self (z := φ g)).symm
    _ = Complex.normSq (φ g) := by simp

private theorem cfNormSq_nonneg_pf56
    {H : Type*} [Group H] [Finite H]
    (φ : Section1.ClassFunction H) :
    0 ≤ cfNormSq φ := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf56]
  have hcard : 0 ≤ (Nat.card H : ℝ)⁻¹ := by positivity
  have hsum : 0 ≤ ∑ g : H, Complex.normSq (φ g) := by
    refine Finset.sum_nonneg ?_
    intro g _hg
    exact Complex.normSq_nonneg (φ g)
  exact mul_nonneg hcard hsum

private theorem cfNormSq_eq_zero_pf56
    {H : Type*} [Group H] [Finite H]
    {φ : Section1.ClassFunction H}
    (hφ : cfNormSq φ = 0) :
    φ = 0 := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf56] at hφ
  have hcardNat : 0 < Nat.card H := Nat.card_pos
  have hcardReal : 0 < (Nat.card H : ℝ) := by exact_mod_cast hcardNat
  have hcard : 0 < (Nat.card H : ℝ)⁻¹ := inv_pos.mpr hcardReal
  have hsumZero : (∑ g : H, Complex.normSq (φ g)) = 0 := by
    nlinarith
  have hzeroAll :
      ∀ g ∈ (Finset.univ : Finset H), Complex.normSq (φ g) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun g _hg => Complex.normSq_nonneg (φ g))).1 hsumZero
  ext g
  exact Complex.normSq_eq_zero.mp (hzeroAll g (by simp))

private theorem character_eq_zero_of_degree_zero_pf56
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsCharacter χ)
    (hdeg : Section1.degree χ = 0) :
    χ = 0 := by
  rcases hχ with ⟨V, _hadd, _hmod, _hfd, ρ, rfl⟩
  have hfinC : (Module.finrank ℂ V : ℂ) = 0 := by
    simpa [Section1.degree_representation_character ρ] using hdeg
  have hfin : Module.finrank ℂ V = 0 := by
    exact_mod_cast hfinC
  have hsub : Subsingleton V := Module.finrank_zero_iff.mp hfin
  ext g
  have hzero : (ρ g : V →ₗ[ℂ] V) = 0 := by
    ext v
    exact hsub.elim _ _
  simp [Representation.character, hzero]

private theorem degree_eq_nat_of_isCharacter_pf56
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsCharacter χ) :
    ∃ d : ℕ, Section1.degree χ = (d : ℂ) := by
  rcases hχ with ⟨V, _hadd, _hmod, _hfd, ρ, rfl⟩
  exact ⟨Module.finrank ℂ V, Section1.degree_representation_character ρ⟩

private theorem isVirtualCharacter_of_signedIrreducible_pf56
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Theory.Character.IsVirtualCharacter χ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hμ
  · simpa using Section3.isVirtualCharacter_neg
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hμ)


private theorem scalarProduct_weightedFamilySum_left_pf56
    {G ι : Type*} [Finite G] [Finite ι]
    (w : ι → ℂ) (μ : ι → Section1.ClassFunction G)
    (φ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Section1.weightedFamilySum w μ) φ =
      ∑ i : ι, w i * Section1.scalarProduct G (μ i) φ := by
  classical
  change Section1.scalarProduct G (fun g : G => ∑ i : ι, w i * μ i g) φ = _
  rw [Section1.scalarProduct_fintype_sum_left]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change Section1.scalarProduct G (w i • μ i) φ = _
  rw [Section1.scalarProduct_smul_left]

private theorem scalarProduct_weightedFamilySum_left_orthogonal_real_pf56
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (w : ι → ℝ) (μ : ι → Section1.ClassFunction G) (r : ι → ℝ)
    (horth :
      ∀ i j : ι, i ≠ j → Section1.scalarProduct G (μ i) (μ j) = 0)
    (hself : ∀ i : ι, Section1.scalarProduct G (μ i) (μ i) = (r i : ℂ))
    (j : ι) :
    Section1.scalarProduct G
        (Section1.weightedFamilySum (fun i => (w i : ℂ)) μ) (μ j) =
      ((w j * r j : ℝ) : ℂ) := by
  classical
  rw [scalarProduct_weightedFamilySum_left_pf56]
  calc
    (∑ i : ι, ((w i : ℂ) * Section1.scalarProduct G (μ i) (μ j))) =
        ∑ i : ι, if i = j then (((w i * r i : ℝ) : ℂ)) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hij : i = j
          · subst hij
            simp [hself]
          · simp [horth i j hij, hij]
    _ = ((w j * r j : ℝ) : ℂ) := by
          simp

private theorem cfNormSq_weightedFamilySum_orthogonal_real_pf56
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (w : ι → ℝ) (μ : ι → Section1.ClassFunction G) (r : ι → ℝ)
    (horth :
      ∀ i j : ι, i ≠ j → Section1.scalarProduct G (μ i) (μ j) = 0)
    (hself : ∀ i : ι, Section1.scalarProduct G (μ i) (μ i) = (r i : ℂ)) :
    cfNormSq (Section1.weightedFamilySum (fun i => (w i : ℂ)) μ) =
      ∑ i : ι, (w i) ^ (2 : ℕ) * r i := by
  classical
  unfold cfNormSq
  rw [scalarProduct_weightedFamilySum_left_pf56]
  have hright :
      ∀ i : ι,
        Section1.scalarProduct G (μ i)
            (Section1.weightedFamilySum (fun j => (w j : ℂ)) μ) =
          ((w i * r i : ℝ) : ℂ) := by
    intro i
    calc
      Section1.scalarProduct G (μ i)
          (Section1.weightedFamilySum (fun j => (w j : ℂ)) μ) =
            ∑ j : ι, star ((w j : ℂ)) * Section1.scalarProduct G (μ i) (μ j) := by
              simpa using
                (Section1.scalarProduct_weightedFamilySum_right
                  (G := G) (ι := ι) (phi := μ i) (w := fun j => (w j : ℂ)) (psi := μ))
      _ = ∑ j : ι, if j = i then ((((w j) * r j : ℝ) : ℂ)) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            by_cases hji : j = i
            · subst hji
              simp [hself]
            · have hij : i ≠ j := by
                intro hij
                exact hji hij.symm
              simp [horth i j hij, hji]
      _ = ((w i * r i : ℝ) : ℂ) := by
            simp
  calc
    Complex.re
        (∑ i : ι,
          (w i : ℂ) *
            Section1.scalarProduct G (μ i)
              (Section1.weightedFamilySum (fun j => (w j : ℂ)) μ)) =
        Complex.re (∑ i : ι, (((w i) ^ (2 : ℕ) * r i : ℝ) : ℂ)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hright i]
          simp [pow_two, mul_left_comm, mul_comm]
    _ = ∑ i : ι, (w i) ^ (2 : ℕ) * r i := by
          simp [pow_two]

private theorem isVirtualCharacter_zsmul_pf56
    {G : Type u} [Group G] [Finite G]
    (n : ℤ) {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (n • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isVirtualCharacter_finset_sum_pf56
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} (s : Finset ι) (Φ : ι → Section1.ClassFunction G)
    (hΦ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Φ i)) :
    Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, (fun i => nomatch i), (fun i => nomatch i), (fun i => nomatch i), ?_⟩
      ext g
      simp [Theory.Character.virtualCharacterOfRepresentations]
  | @insert a s ha ih =>
      have ha' : Theory.Character.IsVirtualCharacter (Φ a) := hΦ a (Finset.mem_insert_self a s)
      have hs' : Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
        refine ih ?_
        intro i hi
        exact hΦ i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'

private theorem isVirtualCharacter_evalCoeff_pf56
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G)
    (hμ : ∀ i, Theory.Character.IsVirtualCharacter (μ i))
    (v : Section1.CoeffVector ι) :
    Theory.Character.IsVirtualCharacter (Section1.evalCoeff μ v) := by
  classical
  rw [Section1.evalCoeff]
  refine isVirtualCharacter_finset_sum_pf56 (Finset.univ : Finset ι)
    (fun i => ((v i : ℂ) • μ i)) ?_
  intro i _hi
  have hsmul :
      (v i : ℂ) • μ i = (v i • μ i : Section1.ClassFunction G) := by
    ext g
    simp [zsmul_eq_mul]
  rw [hsmul]
  exact isVirtualCharacter_zsmul_pf56 (v i) (hμ i)

private theorem scalarProduct_self_eq_cfNormSq_of_character_pf56
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

private theorem map_evalCoeff_pf56
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

private theorem scalarProduct_evalCoeff_left_zero_pf56
    {G ι : Type*} [Finite G] [Fintype ι]
    (μ : ι → Section1.ClassFunction G)
    (v : Section1.CoeffVector ι)
    {φ : Section1.ClassFunction G}
    (hzero : ∀ i, Section1.scalarProduct G (μ i) φ = 0) :
    Section1.scalarProduct G (Section1.evalCoeff μ v) φ = 0 := by
  rw [Section1.evalCoeff]
  have hsumfun :
      (∑ i : ι, (v i : ℂ) • μ i) =
        (fun g : G => ∑ i : ι, ((v i : ℂ) • μ i) g) := by
    ext g
    simp
  rw [hsumfun]
  rw [Section1.scalarProduct_fintype_sum_left]
  refine Finset.sum_eq_zero ?_
  intro i _hi
  rw [Section1.scalarProduct_smul_left, hzero i, mul_zero]

private theorem scalarProduct_evalCoeff_eq_of_gram_eq_pf56
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

private theorem scalarProduct_old_transform_eq_source_of_degree_ne_zero_pf56
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S S1 : Finset (Section1.ClassFunction L))
    (T τ1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ θ : Section1.ClassFunction L)
    (h52 : hypothesis_5_2_statement S T)
    (hS1S : S1 ⊆ S)
    (hτ1_agree : agreesOnIntegerSpanOn S1 puncturedSet T τ1)
    (hψ_span : integerSpan S1 ψ)
    (dψ : ℤ)
    (dS1 : S1 → ℤ)
    (hψ_degree : Section1.degree ψ = (dψ : ℂ))
    (hdψ_ne : (dψ : ℂ) ≠ 0)
    (hS1_degree :
      ∀ Y0 : S1, Section1.degree (Y0 : Section1.ClassFunction L) =
        (dS1 Y0 : ℂ))
    (hθ_memOn : integerSpanOn S puncturedSet θ)
    (hψ_transfer :
      Section1.scalarProduct G (τ1 ψ) (T θ) =
        Section1.scalarProduct L ψ θ) :
    ∀ Y0 : S1,
      Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) (T θ) =
        Section1.scalarProduct L (Y0 : Section1.ClassFunction L) θ := by
  classical
  rcases h52 with ⟨_hsetup, _R, _h52a, h52b, _h52c, _h52d, _h52e⟩
  intro Y0
  let η : Section1.ClassFunction L :=
    (dψ : ℂ) • (Y0 : Section1.ClassFunction L) - (dS1 Y0 : ℂ) • ψ
  have hη_span_S1 : integerSpan S1 η := by
    dsimp [η]
    exact integerSpan_sub_pf56
      (integerSpan_zsmul_pf56 dψ (integerSpan_of_mem_pf56 S1 Y0.2))
      (integerSpan_zsmul_pf56 (dS1 Y0) hψ_span)
  have hη_on : Section1.supportedOn η puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf56 η).2
    rw [Section1.degree_apply]
    have hY0eval : (Y0 : Section1.ClassFunction L) 1 = (dS1 Y0 : ℂ) := by
      simpa [Section1.degree_apply] using hS1_degree Y0
    have hψeval : ψ 1 = (dψ : ℂ) := by
      simpa [Section1.degree_apply] using hψ_degree
    simp [η, hY0eval, hψeval, mul_comm]
  have hη_memOn_S : integerSpanOn S puncturedSet η :=
    ⟨integerSpan_mono_pf56 hS1S hη_span_S1, hη_on⟩
  have hη_agree : τ1 η = T η :=
    hτ1_agree η ⟨hη_span_S1, hη_on⟩
  have htransfer :
      Section1.scalarProduct G (τ1 η) (T θ) =
        Section1.scalarProduct L η θ := by
    rw [hη_agree]
    exact h52b.1 η θ hη_memOn_S hθ_memOn
  have htarget_expand :
      Section1.scalarProduct G (τ1 η) (T θ) =
        (dψ : ℂ) *
            Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) (T θ) -
          (dS1 Y0 : ℂ) * Section1.scalarProduct G (τ1 ψ) (T θ) := by
    dsimp [η]
    rw [map_sub, map_smul, map_smul, scalarProduct_sub_left_pf56,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
  have hsource_expand :
      Section1.scalarProduct L η θ =
        (dψ : ℂ) * Section1.scalarProduct L (Y0 : Section1.ClassFunction L) θ -
          (dS1 Y0 : ℂ) * Section1.scalarProduct L ψ θ := by
    dsimp [η]
    rw [scalarProduct_sub_left_pf56, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_left]
  have hmain :
      (dψ : ℂ) *
          Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) (T θ) =
        (dψ : ℂ) *
          Section1.scalarProduct L (Y0 : Section1.ClassFunction L) θ := by
    have h := htransfer
    rw [htarget_expand, hsource_expand, hψ_transfer] at h
    have h' := congrArg
      (fun z : ℂ => z + (dS1 Y0 : ℂ) * Section1.scalarProduct L ψ θ) h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm] using h'
  exact mul_left_cancel₀ hdψ_ne hmain

private theorem int_eq_zero_of_quadratic_bound_pf56
    (a d1 : ℕ) (A : ℤ) (sumDegNorm : ℝ)
    (hd1_sq_pos : 0 < (d1 : ℝ) ^ (2 : ℕ))
    (hsumDegNorm_gt : 2 * (a : ℝ) * (d1 : ℝ) ^ (2 : ℕ) < sumDegNorm)
    (hsumDegNorm_pos : 0 < sumDegNorm)
    (hAineq :
      ((A : ℝ) ^ (2 : ℕ) / (d1 : ℝ) ^ (2 : ℕ)) * sumDegNorm -
        2 * (a : ℝ) * (A : ℝ) ≤ 0) :
    A = 0 := by
  have hd1_sq_ne : (d1 : ℝ) ^ (2 : ℕ) ≠ 0 := by
    positivity
  have hfactor :
      (A : ℝ) * (d1 : ℝ) ^ (2 : ℕ) *
          ((A : ℝ) * sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) - 2 * (a : ℝ)) ≤
        0 := by
    have hmul := mul_le_mul_of_nonneg_right hAineq (le_of_lt hd1_sq_pos)
    have htmp := hmul
    field_simp [hd1_sq_ne] at htmp
    simpa using htmp
  by_contra hA_ne
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hAnegR : (A : ℝ) < 0 := by exact_mod_cast hA_neg
    have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
    have hsumDivPos : 0 < sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) := by
      exact div_pos hsumDegNorm_pos hd1_sq_pos
    have hfac1_neg : (A : ℝ) * (d1 : ℝ) ^ (2 : ℕ) < 0 := by
      nlinarith
    have hfac2_neg :
        (A : ℝ) * sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) - 2 * (a : ℝ) < 0 := by
      have hAdiv_neg' : (A : ℝ) * (sumDegNorm / (d1 : ℝ) ^ (2 : ℕ)) < 0 := by
        exact mul_neg_of_neg_of_pos hAnegR hsumDivPos
      have hAdiv_neg : (A : ℝ) * sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) < 0 := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hAdiv_neg'
      nlinarith
    have hpos :
        0 <
          (A : ℝ) * (d1 : ℝ) ^ (2 : ℕ) *
            ((A : ℝ) * sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) - 2 * (a : ℝ)) := by
      exact mul_pos_of_neg_of_neg hfac1_neg hfac2_neg
    exact (not_lt_of_ge hfactor) hpos
  · have hAposR : 0 < (A : ℝ) := by exact_mod_cast hA_pos
    have hAone : (1 : ℤ) ≤ A := Int.add_one_le_iff.mpr hA_pos
    have hAoneR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hAone
    have hsumDivGt : 2 * (a : ℝ) < sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) := by
      exact (lt_div_iff₀ hd1_sq_pos).2 hsumDegNorm_gt
    have hsumDivPos : 0 < sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) := by
      exact div_pos hsumDegNorm_pos hd1_sq_pos
    have hfac1_pos : 0 < (A : ℝ) * (d1 : ℝ) ^ (2 : ℕ) := by
      positivity
    have hfac2_pos :
        0 <
          (A : ℝ) * sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) - 2 * (a : ℝ) := by
      have hmul_ge' :
          sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) ≤
            (A : ℝ) * (sumDegNorm / (d1 : ℝ) ^ (2 : ℕ)) := by
        have := mul_le_mul_of_nonneg_right hAoneR (le_of_lt hsumDivPos)
        simpa [one_mul] using this
      have hmul_ge :
          sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) ≤
            (A : ℝ) * sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul_ge'
      have hmain :
          2 * (a : ℝ) <
            (A : ℝ) * sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) :=
        lt_of_lt_of_le hsumDivGt hmul_ge
      linarith
    have hpos :
        0 <
          (A : ℝ) * (d1 : ℝ) ^ (2 : ℕ) *
            ((A : ℝ) * sumDegNorm / (d1 : ℝ) ^ (2 : ℕ) - 2 * (a : ℝ)) := by
      exact mul_pos hfac1_pos hfac2_pos
    exact (not_lt_of_ge hfactor) hpos

private theorem orthogonal_projection_decomposition_pf56
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R)
    {η : Section1.ClassFunction G}
    (hηvirt : Theory.Character.IsVirtualCharacter η) :
    ∃ Xbig Y : Section1.ClassFunction G,
      integerSpan R Xbig ∧
      orthogonalToFinset R Y ∧
      η = Xbig - Y := by
  let μ : R → Section1.ClassFunction G := fun a => (a : Section1.ClassFunction G)
  have hμorth :
      ∀ a b : R,
        Section1.scalarProduct G (μ a) (μ b) = if a = b then 1 else 0 :=
    scalarProduct_eq_ite_of_signedOrthonormalFinset_pf56 hR
  let coeffs : Section1.CoeffVector R := fun r =>
    Classical.choose <|
      Section3.scalarProduct_isVirtualCharacter_eq_int
        hηvirt
        (isVirtualCharacter_of_signedIrreducible_pf56 (hR.1 _ r.2))
  have hcoeffs :
      ∀ r : R,
        Section1.scalarProduct G η (μ r) = (coeffs r : ℂ) := by
    intro r
    exact Classical.choose_spec <|
      Section3.scalarProduct_isVirtualCharacter_eq_int
        hηvirt
        (isVirtualCharacter_of_signedIrreducible_pf56 (hR.1 _ r.2))
  let Xbig : Section1.ClassFunction G := Section1.evalCoeff μ coeffs
  let Y : Section1.ClassFunction G := Xbig - η
  refine ⟨Xbig, Y, ?_, ?_, ?_⟩
  · exact ⟨coeffs, rfl⟩
  · intro ψ hψ
    let r : R := ⟨ψ, hψ⟩
    have hXbigCoeff :
        Section1.scalarProduct G Xbig (μ r) = (coeffs r : ℂ) := by
      have hμbasis :
          Section1.evalCoeff μ (Section1.basisVector r) = μ r := by
        ext g
        rw [Section1.evalCoeff, Finset.sum_eq_single r]
        · simp [Section1.basisVector]
        · intro s _hs hsr
          simp [Section1.basisVector, hsr]
        · intro hrFalse
          exact (hrFalse (Finset.mem_univ _)).elim
      rw [← hμbasis]
      calc
        Section1.scalarProduct G Xbig (Section1.evalCoeff μ (Section1.basisVector r)) =
            (Section1.coeffDot coeffs (Section1.basisVector r) : ℂ) := by
              dsimp [Xbig]
              simpa using
                scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf56
                  μ hμorth coeffs (Section1.basisVector r)
        _ = (coeffs r : ℂ) := by
              simp [Section1.coeffDot, Section1.basisVector]
    dsimp [Y]
    rw [scalarProduct_sub_left_pf56]
    simpa [μ] using sub_eq_zero.mpr (hXbigCoeff.trans (hcoeffs r).symm)
  · dsimp [Y]
    ext g
    simp

private theorem cfNormSq_natCast_smul_pf56
    {G : Type*} [Group G] [Finite G]
    (a : ℕ) (φ : Section1.ClassFunction G) :
    cfNormSq ((a : ℂ) • φ) = (a : ℝ) ^ (2 : ℕ) * cfNormSq φ := by
  unfold cfNormSq
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
  simp [pow_two, mul_assoc, mul_left_comm]

private theorem scalarProduct_sum_right_zero_of_orthogonalToFinset_pf56
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    {φ : Section1.ClassFunction G}
    (horth : orthogonalToFinset R φ) :
    Section1.scalarProduct G φ (Finset.sum R fun ψ => ψ) = 0 := by
  classical
  induction R using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert ψ R hψR ih =>
      have horth_tail : orthogonalToFinset R φ := by
        intro η hη
        exact horth (Finset.mem_insert_of_mem hη)
      rw [Finset.sum_insert hψR, scalarProduct_add_right_pf56, ih horth_tail]
      simp [horth (Finset.mem_insert_self ψ R)]


private theorem theorem_5_6_3_extend_from_candidate_pf56
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S1 : Finset (Section1.ClassFunction L))
    (T τ1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ χbar ψ : Section1.ClassFunction L)
    (X Xbar : Section1.ClassFunction G)
    (hψ_span : integerSpan S1 ψ)
    (hχnotS1 : χ ∉ S1)
    (hχbarnotS1 : χbar ∉ S1)
    (hχ_ne_χbar : χ ≠ χbar)
    (hχ_self_ne : Section1.scalarProduct L χ χ ≠ 0)
    (hχbar_self_ne : Section1.scalarProduct L χbar χbar ≠ 0)
    (hχ_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χ = 0)
    (hχbar_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χbar = 0)
    (hχbarχ_zero : Section1.scalarProduct L χbar χ = 0)
    (hχχbar_zero : Section1.scalarProduct L χ χbar = 0)
    (hτ1_iso : isCFLinearIsometryOnSpan S1 τ1)
    (hτ1_virt : mapsIntegerSpanToVirtualCharacters S1 τ1)
    (hτ1_agree : agreesOnIntegerSpanOn S1 puncturedSet T τ1)
    (hX_virt : Theory.Character.IsVirtualCharacter X)
    (hXbar_virt : Theory.Character.IsVirtualCharacter Xbar)
    (hOld_X_zero :
      ∀ Y0 : S1, Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) X = 0)
    (hX_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct G X (τ1 (Y0 : Section1.ClassFunction L)) = 0)
    (hOld_Xbar_zero :
      ∀ Y0 : S1, Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) Xbar = 0)
    (hXbar_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct G Xbar (τ1 (Y0 : Section1.ClassFunction L)) = 0)
    (hX_self : Section1.scalarProduct G X X = Section1.scalarProduct L χ χ)
    (hXbar_self :
      Section1.scalarProduct G Xbar Xbar = Section1.scalarProduct L χbar χbar)
    (hX_Xbar_zero : Section1.scalarProduct G X Xbar = 0)
    (hXbar_X_zero : Section1.scalarProduct G Xbar X = 0)
    (hdiffψ_on : Section1.supportedOn (χ - ψ) puncturedSet)
    (hdiffχ_on : Section1.supportedOn (χ - χbar) puncturedSet)
    (hTdiffψ : X - τ1 ψ = T (χ - ψ))
    (hTdiffχ : X - Xbar = T (χ - χbar)) :
    ∃ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
      isCFLinearIsometryOnSpan (S1 ∪ {χ, χbar}) Tnew ∧
        mapsIntegerSpanToVirtualCharacters (S1 ∪ {χ, χbar}) Tnew ∧
          agreesOnIntegerSpanOn (S1 ∪ {χ, χbar}) puncturedSet T Tnew := by
  classical
  let pair : Finset (Section1.ClassFunction L) := {χ, χbar}
  let Snew : Finset (Section1.ClassFunction L) := S1 ∪ pair
  have hχ_mem_Snew : χ ∈ Snew := by simp [Snew, pair]
  have hχbar_mem_Snew : χbar ∈ Snew := by simp [Snew, pair]
  have hOld_le_Snew : S1 ⊆ Snew := by
    intro η hη
    simp [Snew, hη]
  have hpair_disjoint : Disjoint S1 pair := by
    rw [Finset.disjoint_left]
    intro η hηS1 hηpair
    simp [pair] at hηpair
    rcases hηpair with hηχ | hηχbar
    · exact hχnotS1 (hηχ ▸ hηS1)
    · exact hχbarnotS1 (hηχbar ▸ hηS1)
  let coeffχ : Section1.ClassFunction L →ₗ[ℂ] ℂ :=
    { toFun := fun η => (Section1.scalarProduct L χ χ)⁻¹ *
        Section1.scalarProduct L η χ
      map_add' := by
        intro η ξ
        rw [Section1.scalarProduct_add_left]
        simp [mul_add]
      map_smul' := by
        intro z η
        rw [Section1.scalarProduct_smul_left]
        simp [smul_eq_mul, mul_left_comm] }
  let coeffχbar : Section1.ClassFunction L →ₗ[ℂ] ℂ :=
    { toFun := fun η => (Section1.scalarProduct L χbar χbar)⁻¹ *
        Section1.scalarProduct L η χbar
      map_add' := by
        intro η ξ
        rw [Section1.scalarProduct_add_left]
        simp [mul_add]
      map_smul' := by
        intro z η
        rw [Section1.scalarProduct_smul_left]
        simp [smul_eq_mul, mul_left_comm] }
  let Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G :=
    τ1 +
      coeffχ.smulRight (X - τ1 χ) +
        coeffχbar.smulRight (Xbar - τ1 χbar)
  have hcoeffχ_old :
      ∀ Y0 : S1, coeffχ (Y0 : Section1.ClassFunction L) = 0 := by
    intro Y0
    dsimp [coeffχ]
    simp [hχ_old_zero Y0]
  have hcoeffχbar_old :
      ∀ Y0 : S1, coeffχbar (Y0 : Section1.ClassFunction L) = 0 := by
    intro Y0
    dsimp [coeffχbar]
    simp [hχbar_old_zero Y0]
  have hTnew_old :
      ∀ Y0 : S1, Tnew (Y0 : Section1.ClassFunction L) =
        τ1 (Y0 : Section1.ClassFunction L) := by
    intro Y0
    dsimp [Tnew]
    simp [hcoeffχ_old Y0, hcoeffχbar_old Y0]
  have hcoeffχ_self : coeffχ χ = 1 := by
    dsimp [coeffχ]
    field_simp [hχ_self_ne]
  have hcoeffχbar_self : coeffχbar χbar = 1 := by
    dsimp [coeffχbar]
    field_simp [hχbar_self_ne]
  have hcoeffχ_χbar : coeffχ χbar = 0 := by
    dsimp [coeffχ]
    simp [hχbarχ_zero]
  have hcoeffχbar_χ : coeffχbar χ = 0 := by
    dsimp [coeffχbar]
    simp [hχχbar_zero]
  have hTnew_χ : Tnew χ = X := by
    dsimp [Tnew]
    simp [hcoeffχ_self, hcoeffχbar_χ]
  have hTnew_χbar : Tnew χbar = Xbar := by
    dsimp [Tnew]
    simp [hcoeffχ_χbar, hcoeffχbar_self]
  have hTnew_ψ : Tnew ψ = τ1 ψ := by
    rcases hψ_span with ⟨vψ, hvψ⟩
    rw [hvψ, map_evalCoeff_pf56, map_evalCoeff_pf56]
    refine congrArg (fun μ => Section1.evalCoeff μ vψ) ?_
    funext Y0
    exact hTnew_old Y0
  have hTnew_diffψ : Tnew (χ - ψ) = T (χ - ψ) := by
    calc
      Tnew (χ - ψ) = Tnew χ - Tnew ψ := by
        simp
      _ = X - τ1 ψ := by rw [hTnew_χ, hTnew_ψ]
      _ = T (χ - ψ) := hTdiffψ
  have hTnew_diffχ : Tnew (χ - χbar) = T (χ - χbar) := by
    calc
      Tnew (χ - χbar) = Tnew χ - Tnew χbar := by
        simp
      _ = X - Xbar := by rw [hTnew_χ, hTnew_χbar]
      _ = T (χ - χbar) := hTdiffχ
  let μSnew : Snew → Section1.ClassFunction L := fun Y => (Y : Section1.ClassFunction L)
  let νSnew : Snew → Section1.ClassFunction G :=
    fun Y => Tnew (Y : Section1.ClassFunction L)
  have hgramSnew :
      ∀ i j : Snew,
        Section1.scalarProduct G (νSnew i) (νSnew j) =
          Section1.scalarProduct L (μSnew i) (μSnew j) := by
    intro i j
    by_cases hiOld : (i : Section1.ClassFunction L) ∈ S1
    · by_cases hjOld : (j : Section1.ClassFunction L) ∈ S1
      · let iOld : S1 := ⟨(i : Section1.ClassFunction L), hiOld⟩
        let jOld : S1 := ⟨(j : Section1.ClassFunction L), hjOld⟩
        calc
          Section1.scalarProduct G (νSnew i) (νSnew j) =
              Section1.scalarProduct G
                (Tnew (iOld : Section1.ClassFunction L))
                (Tnew (jOld : Section1.ClassFunction L)) := by
                  simp [νSnew, iOld, jOld]
          _ = Section1.scalarProduct G
                (τ1 (iOld : Section1.ClassFunction L))
                (τ1 (jOld : Section1.ClassFunction L)) := by
                  rw [hTnew_old iOld, hTnew_old jOld]
          _ = Section1.scalarProduct L
                (iOld : Section1.ClassFunction L)
                (jOld : Section1.ClassFunction L) := by
                  exact hτ1_iso _ _
                    (integerSpan_of_mem_pf56 S1 iOld.2)
                    (integerSpan_of_mem_pf56 S1 jOld.2)
          _ = Section1.scalarProduct L (μSnew i) (μSnew j) := by
                simp [μSnew, iOld, jOld]
      · have hjpair : (j : Section1.ClassFunction L) ∈ pair := by
          have hjSnew : (j : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact j.2
          exact (Finset.mem_union.mp hjSnew).resolve_left hjOld
        have hjpair_eq :
            (j : Section1.ClassFunction L) = χ ∨
              (j : Section1.ClassFunction L) = χbar := by
          simpa [pair] using hjpair
        rcases hjpair_eq with hjχ | hjχbar
        · have hsrc :
              Section1.scalarProduct L (i : Section1.ClassFunction L) χ = 0 :=
            hχ_old_zero ⟨(i : Section1.ClassFunction L), hiOld⟩
          have hzero := hOld_X_zero ⟨(i : Section1.ClassFunction L), hiOld⟩
          rw [← hTnew_old ⟨(i : Section1.ClassFunction L), hiOld⟩] at hzero
          simpa [νSnew, μSnew, hTnew_χ, hsrc, hjχ] using hzero
        · have hsrc :
              Section1.scalarProduct L (i : Section1.ClassFunction L) χbar = 0 :=
            hχbar_old_zero ⟨(i : Section1.ClassFunction L), hiOld⟩
          have hzero := hOld_Xbar_zero ⟨(i : Section1.ClassFunction L), hiOld⟩
          rw [← hTnew_old ⟨(i : Section1.ClassFunction L), hiOld⟩] at hzero
          simpa [νSnew, μSnew, hTnew_χbar, hsrc, hjχbar] using hzero
    · by_cases hjOld : (j : Section1.ClassFunction L) ∈ S1
      · have hipair : (i : Section1.ClassFunction L) ∈ pair := by
          have hiSnew : (i : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact i.2
          exact (Finset.mem_union.mp hiSnew).resolve_left hiOld
        have hipair_eq :
            (i : Section1.ClassFunction L) = χ ∨
              (i : Section1.ClassFunction L) = χbar := by
          simpa [pair] using hipair
        rcases hipair_eq with hiχ | hiχbar
        · have hsrc :
              Section1.scalarProduct L χ (j : Section1.ClassFunction L) = 0 :=
            scalarProduct_zero_swap_pf56
              (hχ_old_zero ⟨(j : Section1.ClassFunction L), hjOld⟩)
          have hzero := hX_old_zero ⟨(j : Section1.ClassFunction L), hjOld⟩
          rw [← hTnew_old ⟨(j : Section1.ClassFunction L), hjOld⟩] at hzero
          simpa [νSnew, μSnew, hTnew_χ, hsrc, hiχ] using hzero
        · have hsrc :
              Section1.scalarProduct L χbar (j : Section1.ClassFunction L) = 0 :=
            scalarProduct_zero_swap_pf56
              (hχbar_old_zero ⟨(j : Section1.ClassFunction L), hjOld⟩)
          have hzero := hXbar_old_zero ⟨(j : Section1.ClassFunction L), hjOld⟩
          rw [← hTnew_old ⟨(j : Section1.ClassFunction L), hjOld⟩] at hzero
          simpa [νSnew, μSnew, hTnew_χbar, hsrc, hiχbar] using hzero
      · have hipair : (i : Section1.ClassFunction L) = χ ∨
            (i : Section1.ClassFunction L) = χbar := by
          have hiSnew : (i : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact i.2
          have hipair' : (i : Section1.ClassFunction L) ∈ pair :=
            (Finset.mem_union.mp hiSnew).resolve_left hiOld
          simpa [pair] using hipair'
        have hjpair : (j : Section1.ClassFunction L) = χ ∨
            (j : Section1.ClassFunction L) = χbar := by
          have hjSnew : (j : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact j.2
          have hjpair' : (j : Section1.ClassFunction L) ∈ pair :=
            (Finset.mem_union.mp hjSnew).resolve_left hjOld
          simpa [pair] using hjpair'
        rcases hipair with hiχ | hiχbar <;> rcases hjpair with hjχ | hjχbar
        · simpa [νSnew, μSnew, hTnew_χ, hiχ, hjχ] using hX_self
        · simpa [νSnew, μSnew, hTnew_χ, hTnew_χbar, hiχ, hjχbar,
            hχχbar_zero] using hX_Xbar_zero
        · simpa [νSnew, μSnew, hTnew_χ, hTnew_χbar, hiχbar, hjχ,
            hχbarχ_zero] using hXbar_X_zero
        · simpa [νSnew, μSnew, hTnew_χbar, hiχbar, hjχbar] using hXbar_self
  have hIsoNew :
      isCFLinearIsometryOnSpan Snew Tnew := by
    intro η ξ hη hξ
    rcases hη with ⟨v, hv⟩
    rcases hξ with ⟨w, hw⟩
    rw [hv, hw, map_evalCoeff_pf56, map_evalCoeff_pf56]
    simpa [μSnew, νSnew] using
      scalarProduct_evalCoeff_eq_of_gram_eq_pf56 μSnew νSnew hgramSnew v w
  have hVirtNew :
      mapsIntegerSpanToVirtualCharacters Snew Tnew := by
    intro η hη
    rcases hη with ⟨v, hv⟩
    let μT : Snew → Section1.ClassFunction G :=
      fun Y => Tnew (Y : Section1.ClassFunction L)
    have hμTvirt : ∀ Y : Snew, Theory.Character.IsVirtualCharacter (μT Y) := by
      intro Y
      by_cases hYold : (Y : Section1.ClassFunction L) ∈ S1
      · let Y0 : S1 := ⟨(Y : Section1.ClassFunction L), hYold⟩
        have hYspan : integerSpan S1 (Y0 : Section1.ClassFunction L) :=
          integerSpan_of_mem_pf56 S1 Y0.2
        have hvirt := hτ1_virt (Y0 : Section1.ClassFunction L) hYspan
        rw [← hTnew_old Y0] at hvirt
        simpa [μT, Y0] using hvirt
      · have hYpair : (Y : Section1.ClassFunction L) = χ ∨
            (Y : Section1.ClassFunction L) = χbar := by
          have hYSnew : (Y : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact Y.2
          have hYpair' : (Y : Section1.ClassFunction L) ∈ pair :=
            (Finset.mem_union.mp hYSnew).resolve_left hYold
          simpa [pair] using hYpair'
        rcases hYpair with hYχ | hYχbar
        · simpa [μT, hTnew_χ, hYχ] using hX_virt
        · simpa [μT, hTnew_χbar, hYχbar] using hXbar_virt
    rw [hv, map_evalCoeff_pf56]
    exact isVirtualCharacter_evalCoeff_pf56 μT hμTvirt v
  have hAgreeNew :
      agreesOnIntegerSpanOn Snew puncturedSet T Tnew := by
    intro η hη
    rcases hη with ⟨hηspan, hηon⟩
    rcases hηspan with ⟨v, hv⟩
    let vOld : Section1.CoeffVector S1 := fun Y0 =>
      v ⟨(Y0 : Section1.ClassFunction L), hOld_le_Snew Y0.2⟩
    let m : Int := v ⟨χ, hχ_mem_Snew⟩
    let n : Int := v ⟨χbar, hχbar_mem_Snew⟩
    let s : Int := m + n
    let oldSum : Section1.ClassFunction L :=
      Section1.evalCoeff (fun Y0 : S1 => (Y0 : Section1.ClassFunction L)) vOld
    let oldPart : Section1.ClassFunction L := oldSum + (s : ℂ) • ψ
    have hη_split :
        η = oldSum + (m : ℂ) • χ + (n : ℂ) • χbar := by
      rw [hv]
      ext g
      let coeff : Section1.ClassFunction L → ℂ := fun φ =>
        if hφ : φ ∈ Snew then (v ⟨φ, hφ⟩ : ℂ) else 0
      have hsplit :
          Finset.sum Snew (fun φ => coeff φ * φ g) =
            Finset.sum S1 (fun φ => coeff φ * φ g) +
              Finset.sum pair (fun φ => coeff φ * φ g) := by
        rw [show Snew = S1 ∪ pair by rfl, Finset.sum_union hpair_disjoint]
      have hleft :
          (∑ x : Snew, (v x : ℂ) • (x : Section1.ClassFunction L)) g =
            Finset.sum Snew (fun φ => coeff φ * φ g) := by
        rw [Finset.sum_apply, Finset.univ_eq_attach]
        calc
          ∑ x ∈ Snew.attach, ((v x : ℂ) • x.1) g
              = ∑ x ∈ Snew.attach, coeff x.1 * x.1 g := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  have hcoeffx : coeff x.1 = (v x : ℂ) := by
                    simp [coeff, x.2]
                  calc
                    ((v x : ℂ) • x.1) g = (v x : ℂ) * x.1 g := by
                      simp [smul_eq_mul]
                    _ = coeff x.1 * x.1 g := by
                      rw [← hcoeffx]
          _ = Finset.sum Snew (fun φ => coeff φ * φ g) := by
                exact Snew.sum_attach (f := fun φ => coeff φ * φ g)
      have hold :
          oldSum g = Finset.sum S1 (fun φ => coeff φ * φ g) := by
        rw [show oldSum = Section1.evalCoeff
            (fun Y0 : S1 => (Y0 : Section1.ClassFunction L)) vOld by rfl]
        rw [Section1.evalCoeff, Finset.sum_apply, Finset.univ_eq_attach]
        calc
          ∑ x ∈ S1.attach, ((vOld x : ℂ) • x.1) g
              = ∑ x ∈ S1.attach, coeff x.1 * x.1 g := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  have hxSnew : (x : Section1.ClassFunction L) ∈ Snew :=
                    hOld_le_Snew x.2
                  have hcoeffx : coeff x.1 = (vOld x : ℂ) := by
                    simp [vOld, coeff, hxSnew]
                  calc
                    ((vOld x : ℂ) • x.1) g = (vOld x : ℂ) * x.1 g := by
                      simp [smul_eq_mul]
                    _ = coeff x.1 * x.1 g := by
                      rw [← hcoeffx]
          _ = Finset.sum S1 (fun φ => coeff φ * φ g) := by
                exact S1.sum_attach (f := fun φ => coeff φ * φ g)
      have hpairsum :
          Finset.sum pair (fun φ => coeff φ * φ g) =
            (m : ℂ) * χ g + (n : ℂ) * χbar g := by
        rw [show pair = ({χ, χbar} : Finset (Section1.ClassFunction L)) by rfl]
        rw [Finset.sum_insert]
        · rw [Finset.sum_singleton]
          simp [coeff, Snew, pair, m, n]
        · simp [hχ_ne_χbar]
      calc
        (Section1.evalCoeff (fun x : Snew => (x : Section1.ClassFunction L)) v) g
            = (∑ x : Snew, (v x : ℂ) • (x : Section1.ClassFunction L)) g := by
              rfl
        _ = Finset.sum Snew (fun φ => coeff φ * φ g) := hleft
        _ = Finset.sum S1 (fun φ => coeff φ * φ g) +
            Finset.sum pair (fun φ => coeff φ * φ g) := hsplit
        _ = oldSum g +
            ((m : ℂ) * χ g + (n : ℂ) * χbar g) := by
              rw [← hold, hpairsum]
        _ = (oldSum + (m : ℂ) • χ + (n : ℂ) • χbar) g := by
              simp [m, n, add_assoc, smul_eq_mul]
    have hη_decomp :
        η = oldPart + (s : ℂ) • (χ - ψ) - (n : ℂ) • (χ - χbar) := by
      calc
        η = oldSum + (m : ℂ) • χ + (n : ℂ) • χbar := hη_split
        _ = oldPart + (s : ℂ) • (χ - ψ) - (n : ℂ) • (χ - χbar) := by
              ext g
              dsimp [oldPart, oldSum, s, m, n]
              simp [sub_eq_add_neg]
              ring_nf
    have hOldSum_span : integerSpan S1 oldSum := by
      refine ⟨vOld, rfl⟩
    have hOldPart_span : integerSpan S1 oldPart := by
      exact integerSpan_add_pf56 hOldSum_span (integerSpan_zsmul_pf56 s hψ_span)
    have hOldPart_eq :
        oldPart = η + (-(s : ℂ)) • (χ - ψ) + (n : ℂ) • (χ - χbar) := by
      calc
        oldPart = (oldPart + (s : ℂ) • (χ - ψ) -
              (n : ℂ) • (χ - χbar)) +
            (-(s : ℂ)) • (χ - ψ) + (n : ℂ) • (χ - χbar) := by
              ext g
              simp [sub_eq_add_neg]
              ring_nf
        _ = η + (-(s : ℂ)) • (χ - ψ) + (n : ℂ) • (χ - χbar) := by
              rw [hη_decomp]
    have hOldPart_on : Section1.supportedOn oldPart puncturedSet := by
      rw [hOldPart_eq]
      exact supportedOn_add_pf56
        (supportedOn_add_pf56 hηon (supportedOn_smul_pf56 (-(s : ℂ)) hdiffψ_on))
        (supportedOn_smul_pf56 (n : ℂ) hdiffχ_on)
    have hOldPart_memOn : integerSpanOn S1 puncturedSet oldPart :=
      ⟨hOldPart_span, hOldPart_on⟩
    have hTnew_oldSum : Tnew oldSum = τ1 oldSum := by
      dsimp [oldSum, vOld]
      rw [map_evalCoeff_pf56, map_evalCoeff_pf56]
      simp [Section1.evalCoeff, hTnew_old]
    have hTnew_oldPart : Tnew oldPart = τ1 oldPart := by
      dsimp [oldPart]
      simp [map_add, map_smul, hTnew_oldSum, hTnew_ψ]
    calc
      Tnew η = Tnew (oldPart + (s : ℂ) • (χ - ψ) -
          (n : ℂ) • (χ - χbar)) := by rw [hη_decomp]
      _ = Tnew oldPart + (s : ℂ) • Tnew (χ - ψ) -
            (n : ℂ) • Tnew (χ - χbar) := by
            rw [map_sub, map_add, map_smul, map_smul]
      _ = τ1 oldPart + (s : ℂ) • T (χ - ψ) -
            (n : ℂ) • T (χ - χbar) := by
            rw [hTnew_oldPart, hTnew_diffψ, hTnew_diffχ]
      _ = T oldPart + (s : ℂ) • T (χ - ψ) -
            (n : ℂ) • T (χ - χbar) := by
            rw [hτ1_agree oldPart hOldPart_memOn]
      _ = T (oldPart + (s : ℂ) • (χ - ψ) -
            (n : ℂ) • (χ - χbar)) := by
            ext g
            simp [map_add, map_sub, map_smul]
      _ = T η := by rw [hη_decomp]
  exact ⟨Tnew, by simpa [Snew, pair] using hIsoNew,
    by simpa [Snew, pair] using hVirtNew,
    by simpa [Snew, pair] using hAgreeNew⟩

/-- Source part of PF `(5.6.3)` after the checked virtual-character and Gram
reductions: the remaining candidate-image facts are one-sided old-family target
orthogonality for the new conjugate pair. -/
private theorem theorem_5_6_3_extend_coherent_with_candidate_orthogonal_gram_source
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S S1 : Finset (Section1.ClassFunction L))
    (T τ1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ χbar ψ : Section1.ClassFunction L)
    (X Xbar : Section1.ClassFunction G)
    (h52 : hypothesis_5_2_statement S T)
    (hS1S : S1 ⊆ S)
    (hτ1_iso : isCFLinearIsometryOnSpan S1 τ1)
    (_hτ1_virt : mapsIntegerSpanToVirtualCharacters S1 τ1)
    (hτ1_agree : agreesOnIntegerSpanOn S1 puncturedSet T τ1)
    (hψ_span : integerSpan S1 ψ)
    (hχS : χ ∈ S)
    (hχbarS : χbar ∈ S)
    (_hχnotS1 : χ ∉ S1)
    (_hχbarnotS1 : χbar ∉ S1)
    (_hχ_self_ne : Section1.scalarProduct L χ χ ≠ 0)
    (_hχbar_self_ne : Section1.scalarProduct L χbar χbar ≠ 0)
    (hχ_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χ = 0)
    (hχbar_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χbar = 0)
    (_hχbarχ_zero : Section1.scalarProduct L χbar χ = 0)
    (_hχχbar_zero : Section1.scalarProduct L χ χbar = 0)
    (hX_orth_τ1ψ : Section1.scalarProduct G X (τ1 ψ) = 0)
    (hdiffψ_on : Section1.supportedOn (χ - ψ) puncturedSet)
    (hdiffχ_on : Section1.supportedOn (χ - χbar) puncturedSet)
    (dψ : ℤ)
    (hψ_degree : Section1.degree ψ = (dψ : ℂ))
    (hdψ_ne : (dψ : ℂ) ≠ 0)
    (hτ1ψ_Tdiffχ :
      Section1.scalarProduct G (τ1 ψ) (T (χ - χbar)) = 0)
    (htransform : T (χ - ψ) = X - τ1 ψ)
    (hXbar_eq : X - Xbar = T (χ - χbar)) :
    (∀ Y0 : S1,
      Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) X = 0) ∧
      (∀ Y0 : S1,
        Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) Xbar = 0) := by
  classical
  have h52source := h52
  rcases h52 with ⟨hsetup, _R, _h52a, _h52b, _h52c, _h52d, _h52e⟩
  let oldDegreeNat : S1 → ℕ := fun Y0 =>
    Classical.choose
      (degree_eq_nat_of_isCharacter_pf56
        (hsetup.2 ⟨(Y0 : Section1.ClassFunction L), hS1S Y0.2⟩))
  let dS1 : S1 → ℤ := fun Y0 => (oldDegreeNat Y0 : ℤ)
  have hS1_degree :
      ∀ Y0 : S1, Section1.degree (Y0 : Section1.ClassFunction L) =
        (dS1 Y0 : ℂ) := by
    intro Y0
    dsimp [dS1, oldDegreeNat]
    simpa using
      (Classical.choose_spec
        (degree_eq_nat_of_isCharacter_pf56
          (hsetup.2 ⟨(Y0 : Section1.ClassFunction L), hS1S Y0.2⟩)))
  have hχ_span_S : integerSpan S χ := integerSpan_of_mem_pf56 S hχS
  have hψ_span_S : integerSpan S ψ := integerSpan_mono_pf56 hS1S hψ_span
  have hdiffψ_memOn : integerSpanOn S puncturedSet (χ - ψ) :=
    ⟨integerSpan_sub_pf56 hχ_span_S hψ_span_S, hdiffψ_on⟩
  have hχbar_span_S : integerSpan S χbar := integerSpan_of_mem_pf56 S hχbarS
  have hdiffχ_memOn : integerSpanOn S puncturedSet (χ - χbar) :=
    ⟨integerSpan_sub_pf56 hχ_span_S hχbar_span_S, hdiffχ_on⟩
  have hτ1ψ_X : Section1.scalarProduct G (τ1 ψ) X = 0 :=
    scalarProduct_zero_swap_pf56 hX_orth_τ1ψ
  have hψχ_zero : Section1.scalarProduct L ψ χ = 0 := by
    rcases hψ_span with ⟨vψ, hvψ⟩
    rw [hvψ]
    exact scalarProduct_evalCoeff_left_zero_pf56
      (fun Y0 : S1 => (Y0 : Section1.ClassFunction L)) vψ hχ_old_zero
  have hψχbar_zero : Section1.scalarProduct L ψ χbar = 0 := by
    rcases hψ_span with ⟨vψ, hvψ⟩
    rw [hvψ]
    exact scalarProduct_evalCoeff_left_zero_pf56
      (fun Y0 : S1 => (Y0 : Section1.ClassFunction L)) vψ hχbar_old_zero
  have hτ1ψ_self :
      Section1.scalarProduct G (τ1 ψ) (τ1 ψ) =
        Section1.scalarProduct L ψ ψ :=
    hτ1_iso ψ ψ hψ_span hψ_span
  have hψ_transfer_diffψ :
      Section1.scalarProduct G (τ1 ψ) (T (χ - ψ)) =
        Section1.scalarProduct L ψ (χ - ψ) := by
    calc
      Section1.scalarProduct G (τ1 ψ) (T (χ - ψ)) =
          Section1.scalarProduct G (τ1 ψ) (X - τ1 ψ) := by rw [htransform]
      _ = -Section1.scalarProduct G (τ1 ψ) (τ1 ψ) := by
            rw [scalarProduct_sub_right_pf56, hτ1ψ_X]
            simp
      _ = -Section1.scalarProduct L ψ ψ := by rw [hτ1ψ_self]
      _ = Section1.scalarProduct L ψ (χ - ψ) := by
            rw [scalarProduct_sub_right_pf56, hψχ_zero]
            simp
  have hOldTdiffψ :=
    scalarProduct_old_transform_eq_source_of_degree_ne_zero_pf56
      S S1 T τ1 ψ (χ - ψ) h52source
      hS1S hτ1_agree hψ_span dψ dS1 hψ_degree hdψ_ne hS1_degree
      hdiffψ_memOn hψ_transfer_diffψ
  have hψ_transfer_diffχ :
      Section1.scalarProduct G (τ1 ψ) (T (χ - χbar)) =
        Section1.scalarProduct L ψ (χ - χbar) := by
    rw [hτ1ψ_Tdiffχ]
    rw [scalarProduct_sub_right_pf56, hψχ_zero, hψχbar_zero]
    simp
  have hOldTdiffχ :=
    scalarProduct_old_transform_eq_source_of_degree_ne_zero_pf56
      S S1 T τ1 ψ (χ - χbar) h52source
      hS1S hτ1_agree hψ_span dψ dS1 hψ_degree hdψ_ne hS1_degree
      hdiffχ_memOn hψ_transfer_diffχ
  have hX_eq : X = T (χ - ψ) + τ1 ψ := by
    calc
      X = (X - τ1 ψ) + τ1 ψ := by
        ext g
        simp [sub_eq_add_neg]
      _ = T (χ - ψ) + τ1 ψ := by rw [← htransform]
  have hOldX :
      ∀ Y0 : S1,
        Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) X = 0 := by
    intro Y0
    have hτ1Yψ :
        Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) (τ1 ψ) =
          Section1.scalarProduct L (Y0 : Section1.ClassFunction L) ψ :=
      hτ1_iso (Y0 : Section1.ClassFunction L) ψ
        (integerSpan_of_mem_pf56 S1 Y0.2) hψ_span
    rw [hX_eq, scalarProduct_add_right_pf56, hOldTdiffψ Y0, hτ1Yψ,
      scalarProduct_sub_right_pf56, hχ_old_zero Y0]
    simp
  have hXbar_eq' : Xbar = X - T (χ - χbar) := by
    ext g
    have h := congrArg (fun f : Section1.ClassFunction G => f g) hXbar_eq
    have hpoint : X g - Xbar g = (T (χ - χbar)) g := by
      simpa using h
    calc
      Xbar g = X g - (X g - Xbar g) := by ring
      _ = X g - (T (χ - χbar)) g := by rw [hpoint]
      _ = (X - T (χ - χbar)) g := by simp
  have hOldXbar :
      ∀ Y0 : S1,
        Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) Xbar = 0 := by
    intro Y0
    rw [hXbar_eq', scalarProduct_sub_right_pf56, hOldX Y0, hOldTdiffχ Y0,
      scalarProduct_sub_right_pf56, hχ_old_zero Y0, hχbar_old_zero Y0]
    simp
  exact ⟨hOldX, hOldXbar⟩

/-- Source part of PF `(5.6.3)` after the extension-map construction has been
factored out: choose the explicit target image for the conjugate character and
prove its virtuality, then delegate the remaining hard Gram/orthogonality
package. -/
private theorem theorem_5_6_3_extend_coherent_with_candidate_source
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S S1 : Finset (Section1.ClassFunction L))
    (T τ1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ χbar ψ : Section1.ClassFunction L)
    (X : Section1.ClassFunction G)
    (h52 : hypothesis_5_2_statement S T)
    (hS1S : S1 ⊆ S)
    (hτ1_iso : isCFLinearIsometryOnSpan S1 τ1)
    (hτ1_virt : mapsIntegerSpanToVirtualCharacters S1 τ1)
    (hτ1_agree : agreesOnIntegerSpanOn S1 puncturedSet T τ1)
    (hψ_span : integerSpan S1 ψ)
    (hχS : χ ∈ S)
    (hχbarS : χbar ∈ S)
    (hχnotS1 : χ ∉ S1)
    (hχbarnotS1 : χbar ∉ S1)
    (hχ_self_ne : Section1.scalarProduct L χ χ ≠ 0)
    (hχbar_self_ne : Section1.scalarProduct L χbar χbar ≠ 0)
    (hχ_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χ = 0)
    (hχbar_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χbar = 0)
    (hχbarχ_zero : Section1.scalarProduct L χbar χ = 0)
    (hχχbar_zero : Section1.scalarProduct L χ χbar = 0)
    (hX_orth_τ1ψ : Section1.scalarProduct G X (τ1 ψ) = 0)
    (dψ : ℤ)
    (hψ_degree : Section1.degree ψ = (dψ : ℂ))
    (hdψ_ne : (dψ : ℂ) ≠ 0)
    (hτ1ψ_Tdiffχ :
      Section1.scalarProduct G (τ1 ψ) (T (χ - χbar)) = 0)
    (hdiffψ_on : Section1.supportedOn (χ - ψ) puncturedSet)
    (hdiffχ_on : Section1.supportedOn (χ - χbar) puncturedSet)
    (htransform : T (χ - ψ) = X - τ1 ψ) :
    ∃ Xbar : Section1.ClassFunction G,
      Theory.Character.IsVirtualCharacter X ∧
        Theory.Character.IsVirtualCharacter Xbar ∧
          (∀ Y0 : S1,
            Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) X = 0) ∧
          (∀ Y0 : S1,
            Section1.scalarProduct G X (τ1 (Y0 : Section1.ClassFunction L)) = 0) ∧
          (∀ Y0 : S1,
            Section1.scalarProduct G (τ1 (Y0 : Section1.ClassFunction L)) Xbar = 0) ∧
          (∀ Y0 : S1,
            Section1.scalarProduct G Xbar (τ1 (Y0 : Section1.ClassFunction L)) = 0) ∧
          Section1.scalarProduct G X X = Section1.scalarProduct L χ χ ∧
          Section1.scalarProduct G Xbar Xbar =
            Section1.scalarProduct L χbar χbar ∧
          Section1.scalarProduct G X Xbar = 0 ∧
          Section1.scalarProduct G Xbar X = 0 ∧
          X - τ1 ψ = T (χ - ψ) ∧
          X - Xbar = T (χ - χbar) := by
  classical
  have h52source := h52
  rcases h52 with ⟨_hsetup, _R, _h52a, h52b, _h52c, _h52d, _h52e⟩
  let Xbar : Section1.ClassFunction G := X - T (χ - χbar)
  have hXbar_eq : X - Xbar = T (χ - χbar) := by
    ext g
    simp [Xbar, sub_eq_add_neg]
  have hχ_span_S : integerSpan S χ := integerSpan_of_mem_pf56 S hχS
  have hψ_span_S : integerSpan S ψ := integerSpan_mono_pf56 hS1S hψ_span
  have hdiffψ_memOn : integerSpanOn S puncturedSet (χ - ψ) :=
    ⟨integerSpan_sub_pf56 hχ_span_S hψ_span_S, hdiffψ_on⟩
  have hχbar_span_S : integerSpan S χbar := integerSpan_of_mem_pf56 S hχbarS
  have hdiffχ_memOn : integerSpanOn S puncturedSet (χ - χbar) :=
    ⟨integerSpan_sub_pf56 hχ_span_S hχbar_span_S, hdiffχ_on⟩
  have hTdiffψ_virt : Theory.Character.IsVirtualCharacter (T (χ - ψ)) :=
    (h52b.2 (χ - ψ) hdiffψ_memOn).1
  have hTdiffχ_virt : Theory.Character.IsVirtualCharacter (T (χ - χbar)) :=
    (h52b.2 (χ - χbar) hdiffχ_memOn).1
  have hτ1ψ_virt : Theory.Character.IsVirtualCharacter (τ1 ψ) :=
    hτ1_virt ψ hψ_span
  have hτ1ψ_X : Section1.scalarProduct G (τ1 ψ) X = 0 :=
    scalarProduct_zero_swap_pf56 hX_orth_τ1ψ
  have hψχ_zero : Section1.scalarProduct L ψ χ = 0 := by
    rcases hψ_span with ⟨vψ, hvψ⟩
    rw [hvψ]
    exact scalarProduct_evalCoeff_left_zero_pf56
      (fun Y0 : S1 => (Y0 : Section1.ClassFunction L)) vψ hχ_old_zero
  have hχψ_zero : Section1.scalarProduct L χ ψ = 0 :=
    scalarProduct_zero_swap_pf56 hψχ_zero
  have hψχbar_zero : Section1.scalarProduct L ψ χbar = 0 := by
    rcases hψ_span with ⟨vψ, hvψ⟩
    rw [hvψ]
    exact scalarProduct_evalCoeff_left_zero_pf56
      (fun Y0 : S1 => (Y0 : Section1.ClassFunction L)) vψ hχbar_old_zero
  have hsource_diffψ_self :
      Section1.scalarProduct L (χ - ψ) (χ - ψ) =
        Section1.scalarProduct L χ χ + Section1.scalarProduct L ψ ψ := by
    rw [scalarProduct_sub_left_pf56, scalarProduct_sub_right_pf56,
      scalarProduct_sub_right_pf56]
    simp [hχψ_zero, hψχ_zero]
  have htarget_diffψ_self :
      Section1.scalarProduct G (T (χ - ψ)) (T (χ - ψ)) =
        Section1.scalarProduct G X X + Section1.scalarProduct G (τ1 ψ) (τ1 ψ) := by
    rw [htransform, scalarProduct_sub_left_pf56, scalarProduct_sub_right_pf56,
      scalarProduct_sub_right_pf56]
    simp [hX_orth_τ1ψ, hτ1ψ_X]
  have hτ1ψ_self :
      Section1.scalarProduct G (τ1 ψ) (τ1 ψ) =
        Section1.scalarProduct L ψ ψ :=
    hτ1_iso ψ ψ hψ_span hψ_span
  have hTdiffψ_self_iso :=
    h52b.1 (χ - ψ) (χ - ψ) hdiffψ_memOn hdiffψ_memOn
  have hXself :
      Section1.scalarProduct G X X = Section1.scalarProduct L χ χ := by
    have h := hTdiffψ_self_iso
    rw [htarget_diffψ_self, hsource_diffψ_self, hτ1ψ_self] at h
    exact add_right_cancel h
  have hX_eq : X = T (χ - ψ) + τ1 ψ := by
    calc
      X = (X - τ1 ψ) + τ1 ψ := by
        ext g
        simp [sub_eq_add_neg]
      _ = T (χ - ψ) + τ1 ψ := by
        rw [← htransform]
  have hXvirt : Theory.Character.IsVirtualCharacter X := by
    rw [hX_eq]
    exact Section3.isVirtualCharacter_add hTdiffψ_virt hτ1ψ_virt
  have hXbarvirt : Theory.Character.IsVirtualCharacter Xbar := by
    dsimp [Xbar]
    exact Section3.isVirtualCharacter_sub hXvirt hTdiffχ_virt
  rcases theorem_5_6_3_extend_coherent_with_candidate_orthogonal_gram_source
      S S1 T τ1 χ χbar ψ X Xbar h52source hS1S hτ1_iso hτ1_virt
      hτ1_agree hψ_span hχS hχbarS hχnotS1 hχbarnotS1 hχ_self_ne
      hχbar_self_ne hχ_old_zero hχbar_old_zero hχbarχ_zero hχχbar_zero
      hX_orth_τ1ψ hdiffψ_on hdiffχ_on dψ hψ_degree hdψ_ne
      hτ1ψ_Tdiffχ htransform hXbar_eq with
    ⟨hOldX, hOldXbar⟩
  have hXOld :
      ∀ Y0 : S1,
        Section1.scalarProduct G X (τ1 (Y0 : Section1.ClassFunction L)) = 0 := by
    intro Y0
    exact scalarProduct_zero_swap_pf56 (hOldX Y0)
  have hXbarOld :
      ∀ Y0 : S1,
        Section1.scalarProduct G Xbar (τ1 (Y0 : Section1.ClassFunction L)) = 0 := by
    intro Y0
    exact scalarProduct_zero_swap_pf56 (hOldXbar Y0)
  have hτ1ψ_Xbar : Section1.scalarProduct G (τ1 ψ) Xbar = 0 := by
    rcases hψ_span with ⟨vψ, hvψ⟩
    rw [hvψ, map_evalCoeff_pf56]
    exact scalarProduct_evalCoeff_left_zero_pf56
      (fun Y0 : S1 => τ1 (Y0 : Section1.ClassFunction L)) vψ hOldXbar
  have hτ1ψ_X_sub_Xbar :
      Section1.scalarProduct G (τ1 ψ) (X - Xbar) = 0 := by
    rw [scalarProduct_sub_right_pf56, hτ1ψ_X, hτ1ψ_Xbar]
    simp
  have hsource_diffψ_diffχ :
      Section1.scalarProduct L (χ - ψ) (χ - χbar) =
        Section1.scalarProduct L χ χ := by
    rw [scalarProduct_sub_left_pf56, scalarProduct_sub_right_pf56,
      scalarProduct_sub_right_pf56]
    simp [hχχbar_zero, hψχ_zero, hψχbar_zero]
  have htarget_diffψ_diffχ :
      Section1.scalarProduct G (T (χ - ψ)) (T (χ - χbar)) =
        Section1.scalarProduct G X X - Section1.scalarProduct G X Xbar := by
    rw [htransform, ← hXbar_eq, scalarProduct_sub_left_pf56,
      scalarProduct_sub_right_pf56, hτ1ψ_X_sub_Xbar]
    simp
  have hTdiffψ_diffχ_iso :=
    h52b.1 (χ - ψ) (χ - χbar) hdiffψ_memOn hdiffχ_memOn
  have hXXbar : Section1.scalarProduct G X Xbar = 0 := by
    have h := hTdiffψ_diffχ_iso
    rw [htarget_diffψ_diffχ, hsource_diffψ_diffχ, hXself] at h
    exact sub_eq_self.mp h
  have hXbarX : Section1.scalarProduct G Xbar X = 0 :=
    scalarProduct_zero_swap_pf56 hXXbar
  have hsource_diffχ_self :
      Section1.scalarProduct L (χ - χbar) (χ - χbar) =
        Section1.scalarProduct L χ χ + Section1.scalarProduct L χbar χbar := by
    rw [scalarProduct_sub_left_pf56, scalarProduct_sub_right_pf56,
      scalarProduct_sub_right_pf56]
    simp [hχχbar_zero, hχbarχ_zero]
  have hX_X_sub_Xbar :
      Section1.scalarProduct G X (X - Xbar) = Section1.scalarProduct G X X := by
    rw [scalarProduct_sub_right_pf56, hXXbar]
    simp
  have hXbar_X_sub_Xbar :
      Section1.scalarProduct G Xbar (X - Xbar) =
        -Section1.scalarProduct G Xbar Xbar := by
    rw [scalarProduct_sub_right_pf56, hXbarX]
    simp
  have htarget_diffχ_self :
      Section1.scalarProduct G (T (χ - χbar)) (T (χ - χbar)) =
        Section1.scalarProduct G X X + Section1.scalarProduct G Xbar Xbar := by
    have hTdiffχ_eq : T (χ - χbar) = X - Xbar := hXbar_eq.symm
    calc
      Section1.scalarProduct G (T (χ - χbar)) (T (χ - χbar)) =
          Section1.scalarProduct G (X - Xbar) (X - Xbar) := by
            rw [hTdiffχ_eq]
      _ = Section1.scalarProduct G X X + Section1.scalarProduct G Xbar Xbar := by
            rw [scalarProduct_sub_left_pf56, hX_X_sub_Xbar, hXbar_X_sub_Xbar]
            simp
  have hTdiffχ_self_iso :=
    h52b.1 (χ - χbar) (χ - χbar) hdiffχ_memOn hdiffχ_memOn
  have hXbarself :
      Section1.scalarProduct G Xbar Xbar =
        Section1.scalarProduct L χbar χbar := by
    have h := hTdiffχ_self_iso
    rw [htarget_diffχ_self, hsource_diffχ_self, hXself] at h
    exact add_left_cancel h
  exact ⟨Xbar, hXvirt, hXbarvirt, hOldX, hXOld, hOldXbar, hXbarOld,
    hXself, hXbarself, hXXbar, hXbarX, htransform.symm, hXbar_eq⟩


private theorem theorem_5_6_3_extend_coherent_with_extension_source
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S S1 : Finset (Section1.ClassFunction L))
    (T τ1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ φ : Section1.ClassFunction L)
    (c : ℂ)
    (X : Section1.ClassFunction G)
    (h52 : hypothesis_5_2_statement S T)
    (_hS1S : S1 ⊆ S)
    (_hS1closed : ∀ ψ : Section1.ClassFunction L, ψ ∈ S1 →
      Section1.conjugateCharacter ψ ∈ S1)
    (_hτ1_iso : isCFLinearIsometryOnSpan S1 τ1)
    (_hτ1_virt : mapsIntegerSpanToVirtualCharacters S1 τ1)
    (_hτ1_agree : agreesOnIntegerSpanOn S1 puncturedSet T τ1)
    (_hφS1 : φ ∈ S1)
    (_hχS : χ ∈ S)
    (_hχnotS1 : χ ∉ S1)
    (_ha_int : ∃ z : ℤ, c = (z : ℂ))
    (_hdegree : Section1.degree χ = c * Section1.degree φ)
    (_horth : Section1.scalarProduct G X (c • τ1 φ) = 0)
    (_htransform : T (χ - c • φ) = X - c • τ1 φ) :
    ∃ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
      isCFLinearIsometryOnSpan
          (S1 ∪ {χ, Section1.conjugateCharacter χ}) Tnew ∧
        mapsIntegerSpanToVirtualCharacters
          (S1 ∪ {χ, Section1.conjugateCharacter χ}) Tnew ∧
          agreesOnIntegerSpanOn
            (S1 ∪ {χ, Section1.conjugateCharacter χ}) puncturedSet T Tnew := by
  classical
  rcases _ha_int with ⟨z, rfl⟩
  have h52source := h52
  rcases h52 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  let χbar : Section1.ClassFunction L := Section1.conjugateCharacter χ
  let ψ : Section1.ClassFunction L := (z : ℂ) • φ
  have hχbarS : χbar ∈ S := by
    simpa [χbar] using (h52a ⟨χ, _hχS⟩).1
  have hχne : χ ≠ χbar := by
    simpa [χbar] using (h52a ⟨χ, _hχS⟩).2
  have hχbarNotS1 : χbar ∉ S1 := by
    intro hbar
    have hback : Section1.conjugateCharacter χbar ∈ S1 :=
      _hS1closed χbar hbar
    have hcc : Section1.conjugateCharacter χbar = χ := by
      ext g
      simp [χbar, Section1.conjugateCharacter]
    exact _hχnotS1 (by simpa [hcc] using hback)
  have hφ_span_S1 : integerSpan S1 φ := integerSpan_of_mem_pf56 S1 _hφS1
  have hψ_span : integerSpan S1 ψ := by
    dsimp [ψ]
    exact integerSpan_zsmul_pf56 z hφ_span_S1
  have hφchar : Section1.IsCharacter φ :=
    hsetup.2 ⟨φ, _hS1S _hφS1⟩
  obtain ⟨dφ, hdφ⟩ := degree_eq_nat_of_isCharacter_pf56 hφchar
  let dψ : ℤ := z * (dφ : ℤ)
  have hψ_degree : Section1.degree ψ = (dψ : ℂ) := by
    dsimp [ψ, dψ]
    rw [Section1.degree_apply]
    have hφeval : φ 1 = (dφ : ℂ) := by
      simpa [Section1.degree_apply] using hdφ
    simp [hφeval, Int.cast_mul]
  have hχchar : Section1.IsCharacter χ := hsetup.2 ⟨χ, _hχS⟩
  have hχbar_char : Section1.IsCharacter χbar :=
    hsetup.2 ⟨χbar, hχbarS⟩
  have hχ_self_ne : Section1.scalarProduct L χ χ ≠ 0 := by
    have hχ_self := scalarProduct_self_eq_cfNormSq_of_character_pf56 hχchar
    intro hzero
    have hnormC : (cfNormSq χ : ℂ) = 0 := by
      simpa [hχ_self] using hzero
    have hnorm : cfNormSq χ = 0 := by
      exact_mod_cast hnormC
    have hχzero : χ = 0 := cfNormSq_eq_zero_pf56 hnorm
    apply hχne
    calc
      χ = 0 := hχzero
      _ = Section1.conjugateCharacter (0 : Section1.ClassFunction L) := by
            ext g
            simp [Section1.conjugateCharacter]
      _ = χbar := by
            simp [χbar, hχzero]
  have hχ_degree_eq_ψ : Section1.degree χ = Section1.degree ψ := by
    calc
      Section1.degree χ = (z : ℂ) * Section1.degree φ := _hdegree
      _ = Section1.degree ψ := by
            dsimp [ψ]
            rw [Section1.degree_apply]
            simp [Section1.degree_apply]
  have hdψ_ne : (dψ : ℂ) ≠ 0 := by
    intro hdψ_zero
    have hψdeg0 : Section1.degree ψ = 0 := by
      rw [hψ_degree, hdψ_zero]
    have hχdeg0 : Section1.degree χ = 0 := by
      rw [hχ_degree_eq_ψ, hψdeg0]
    have hχzero : χ = 0 := character_eq_zero_of_degree_zero_pf56 hχchar hχdeg0
    have hself0 : Section1.scalarProduct L χ χ = 0 := by
      rw [hχzero]
      simp [Section1.scalarProduct]
    exact hχ_self_ne hself0
  have hχbar_self_ne : Section1.scalarProduct L χbar χbar ≠ 0 := by
    have hχbar_self := scalarProduct_self_eq_cfNormSq_of_character_pf56 hχbar_char
    intro hzero
    have hnormC : (cfNormSq χbar : ℂ) = 0 := by
      simpa [hχbar_self] using hzero
    have hnorm : cfNormSq χbar = 0 := by
      exact_mod_cast hnormC
    have hχbarzero : χbar = 0 := cfNormSq_eq_zero_pf56 hnorm
    have hχ_eq_conj_chibar : χ = Section1.conjugateCharacter χbar := by
      ext g
      simp [χbar, Section1.conjugateCharacter]
    apply hχne
    calc
      χ = Section1.conjugateCharacter χbar := hχ_eq_conj_chibar
      _ = Section1.conjugateCharacter (0 : Section1.ClassFunction L) := by
            rw [hχbarzero]
      _ = 0 := by
            ext g
            simp [Section1.conjugateCharacter]
      _ = χbar := hχbarzero.symm
  have hχ_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χ = 0 := by
    intro Y0
    exact h52c (χ := (Y0 : Section1.ClassFunction L)) (ψ := χ)
      (_hS1S Y0.2) _hχS (by
        intro hEq
        exact _hχnotS1 (hEq.symm ▸ Y0.2))
  have hχbar_old_zero :
      ∀ Y0 : S1, Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χbar = 0 := by
    intro Y0
    exact h52c (χ := (Y0 : Section1.ClassFunction L)) (ψ := χbar)
      (_hS1S Y0.2) hχbarS (by
        intro hEq
        exact hχbarNotS1 (hEq.symm ▸ Y0.2))
  have hχbarχ_zero : Section1.scalarProduct L χbar χ = 0 := by
    exact h52c (χ := χbar) (ψ := χ) hχbarS _hχS (by
      intro hEq
      exact hχne hEq.symm)
  have hχχbar_zero : Section1.scalarProduct L χ χbar = 0 := by
    exact h52c (χ := χ) (ψ := χbar) _hχS hχbarS hχne
  have hφpairIso :
      isCFLinearIsometryOnSpan
        ({φ, Section1.conjugateCharacter φ} :
          Finset (Section1.ClassFunction L)) τ1 := by
    apply isCFLinearIsometryOnSpan_mono_pf56
    · intro η hη
      simp at hη
      rcases hη with rfl | rfl
      · exact _hφS1
      · exact _hS1closed φ _hφS1
    · exact _hτ1_iso
  have hφpairVirt :
      mapsIntegerSpanToVirtualCharacters
        ({φ, Section1.conjugateCharacter φ} :
          Finset (Section1.ClassFunction L)) τ1 := by
    apply mapsIntegerSpanToVirtualCharacters_mono_pf56
    · intro η hη
      simp at hη
      rcases hη with rfl | rfl
      · exact _hφS1
      · exact _hS1closed φ _hφS1
    · exact _hτ1_virt
  have hφdiff_span_S1 :
      integerSpan S1 (φ - Section1.conjugateCharacter φ) := by
    exact integerSpan_sub_pf56 hφ_span_S1
      (integerSpan_of_mem_pf56 S1 (_hS1closed φ _hφS1))
  have hφdiff_on :
      Section1.supportedOn (φ - Section1.conjugateCharacter φ) puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf56 _).2
    rw [Section1.degree_apply]
    change φ 1 - Section1.conjugateCharacter φ 1 = 0
    have hφbar_eval : Section1.conjugateCharacter φ 1 = φ 1 := by
      have hdeg := degree_conjugateCharacter_eq_of_isCharacter hφchar
      simpa [Section1.degree_apply] using hdeg
    simp [hφbar_eval]
  have hφdiffAgree :
      τ1 (φ - Section1.conjugateCharacter φ) =
        T (φ - Section1.conjugateCharacter φ) :=
    _hτ1_agree (φ - Section1.conjugateCharacter φ)
      ⟨hφdiff_span_S1, hφdiff_on⟩
  let φS : S := ⟨φ, _hS1S _hφS1⟩
  let χS : S := ⟨χ, _hχS⟩
  have hτ1φ_subset : isSubsetSumOf (R φS) (τ1 φ) :=
    theorem_5_5 S T R hsetup h52a h52b h52c h52d h52e
      φS τ1 hφpairIso hφpairVirt hφdiffAgree
  have hRφ_Rχ_orth : orthogonalFinsets (R φS) (R χS) := by
    exact h52e χS φS
      (by simpa [φS, χS] using hχ_old_zero ⟨φ, _hφS1⟩)
      (by simpa [φS, χS, χbar] using hχbar_old_zero ⟨φ, _hφS1⟩)
  have hτ1φ_orth_Rχ : orthogonalToFinset (R χS) (τ1 φ) :=
    orthogonalToFinset_of_subsetSum_of_orthogonalFinsets_pf56
      hτ1φ_subset hRφ_Rχ_orth
  have hτ1ψ_eq : τ1 ψ = (z : ℂ) • τ1 φ := by
    dsimp [ψ]
    simp
  have hτ1ψ_orth_Rχ : orthogonalToFinset (R χS) (τ1 ψ) := by
    intro r hr
    rw [hτ1ψ_eq, Section1.scalarProduct_smul_left]
    simp [hτ1φ_orth_Rχ hr]
  have hτ1ψ_Tdiffχ :
      Section1.scalarProduct G (τ1 ψ) (T (χ - χbar)) = 0 := by
    have hTdiffχ := (h52d χS).2
    rw [show χbar = Section1.conjugateCharacter χ by rfl]
    rw [hTdiffχ]
    exact scalarProduct_sum_right_zero_of_orthogonalToFinset_pf56 hτ1ψ_orth_Rχ
  have hdiffψ_on : Section1.supportedOn (χ - ψ) puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf56 _).2
    dsimp [ψ]
    rw [Section1.degree_apply]
    change χ 1 - (z : ℂ) * φ 1 = 0
    have hχeval : χ 1 = (z : ℂ) * φ 1 := by
      simpa [Section1.degree_apply] using _hdegree
    simp [hχeval]
  have hdiffχ_on : Section1.supportedOn (χ - χbar) puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf56 _).2
    rw [Section1.degree_apply]
    change χ 1 - χbar 1 = 0
    have hχbar_eval : χbar 1 = χ 1 := by
      have hdeg := degree_conjugateCharacter_eq_of_isCharacter hχchar
      simpa [χbar, Section1.degree_apply] using hdeg
    simp [hχbar_eval]
  have htransformψ : T (χ - ψ) = X - τ1 ψ := by
    simpa [ψ] using _htransform
  have hX_orth_τ1ψ : Section1.scalarProduct G X (τ1 ψ) = 0 := by
    dsimp [ψ]
    simpa using _horth
  rcases theorem_5_6_3_extend_coherent_with_candidate_source
      S S1 T τ1 χ χbar ψ X h52source _hS1S _hτ1_iso
      _hτ1_virt _hτ1_agree hψ_span _hχS hχbarS _hχnotS1 hχbarNotS1
      hχ_self_ne hχbar_self_ne hχ_old_zero hχbar_old_zero
      hχbarχ_zero hχχbar_zero hX_orth_τ1ψ dψ hψ_degree hdψ_ne
      hτ1ψ_Tdiffχ hdiffψ_on hdiffχ_on htransformψ with
    ⟨Xbar, hXvirt, hXbarvirt, hOldX, hXOld, hOldXbar, hXbarOld,
      hXself, hXbarself, hXXbar, hXbarX, hTdiffψ, hTdiffχ⟩
  rcases theorem_5_6_3_extend_from_candidate_pf56
      S1 T τ1 χ χbar ψ X Xbar hψ_span _hχnotS1 hχbarNotS1
      hχne hχ_self_ne hχbar_self_ne hχ_old_zero hχbar_old_zero
      hχbarχ_zero hχχbar_zero _hτ1_iso _hτ1_virt _hτ1_agree
      hXvirt hXbarvirt hOldX hXOld hOldXbar hXbarOld
      hXself hXbarself hXXbar hXbarX hdiffψ_on hdiffχ_on
      hTdiffψ hTdiffχ with
    ⟨Tnew, hIso, hVirt, hAgree⟩
  exact ⟨Tnew, by simpa [χbar] using hIso,
    by simpa [χbar] using hVirt,
    by simpa [χbar] using hAgree⟩


public theorem theorem_5_6_3_extend_coherent_with
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S S1 : Finset (Section1.ClassFunction L))
    (T τ1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ φ : Section1.ClassFunction L)
    (c : ℂ)
    (X : Section1.ClassFunction G)
    (h52 : hypothesis_5_2_statement S T)
    (_hS1S : S1 ⊆ S)
    (_hS1closed : ∀ ψ : Section1.ClassFunction L, ψ ∈ S1 →
      Section1.conjugateCharacter ψ ∈ S1)
    (_hτ1_iso : isCFLinearIsometryOnSpan S1 τ1)
    (_hτ1_virt : mapsIntegerSpanToVirtualCharacters S1 τ1)
    (_hτ1_agree : agreesOnIntegerSpanOn S1 puncturedSet T τ1)
    (_hφS1 : φ ∈ S1)
    (_hχS : χ ∈ S)
    (_hχnotS1 : χ ∉ S1)
    (_ha_int : ∃ z : ℤ, c = (z : ℂ))
    (_hdegree : Section1.degree χ = c * Section1.degree φ)
    (_horth : Section1.scalarProduct G X (c • τ1 φ) = 0)
    (_htransform : T (χ - c • φ) = X - c • τ1 φ) :
    definition_5_1_statement puncturedSet
      (S1 ∪ {χ, Section1.conjugateCharacter χ}) T := by
  classical
  have h52source := h52
  rcases h52 with ⟨hsetup, R, h52a, _h52b, _h52c, _h52d, _h52e⟩
  have hχbarS : Section1.conjugateCharacter χ ∈ S :=
    (h52a ⟨χ, _hχS⟩).1
  have hχne : χ ≠ Section1.conjugateCharacter χ :=
    (h52a ⟨χ, _hχS⟩).2
  have hχchar : Section1.IsCharacter χ :=
    hsetup.2 ⟨χ, _hχS⟩
  have hsrc :
      sourceVirtualCharacters
        (S1 ∪ {χ, Section1.conjugateCharacter χ}) := by
    intro ψ hψ
    rw [Finset.mem_union] at hψ
    rcases hψ with hψS1 | hψpair
    · exact isVirtualCharacter_of_isCharacter
        (hsetup.2 ⟨ψ, _hS1S hψS1⟩)
    · rw [Finset.mem_insert, Finset.mem_singleton] at hψpair
      rcases hψpair with rfl | rfl
      · exact isVirtualCharacter_of_isCharacter hχchar
      · exact isVirtualCharacter_of_isCharacter
          (hsetup.2 ⟨Section1.conjugateCharacter χ, hχbarS⟩)
  have hnonempty :
      integerSpanOnNonempty
        (S1 ∪ {χ, Section1.conjugateCharacter χ}) puncturedSet := by
    exact integerSpanOnNonempty_of_conjugate_pair
      (by simp) (by simp) hχne hχchar
  rcases theorem_5_6_3_extend_coherent_with_extension_source
      S S1 T τ1 χ φ c X h52source _hS1S _hS1closed
      _hτ1_iso _hτ1_virt _hτ1_agree _hφS1 _hχS _hχnotS1
      _ha_int _hdegree _horth _htransform with
    ⟨Tnew, hIso, hvirt, hagree⟩
  exact ⟨hsrc, hnonempty, Tnew, hIso, hvirt, hagree⟩

set_option linter.tacticAnalysis.introMerge false in
set_option maxHeartbeats 1000000 in
public theorem theorem_5_6
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_5_6_statement S T := by
  intro R hsetup h52a h52b h52c h52d h52e
  intro S1 hS1subset hS1closed X hXbarNotin X1 hcoherent hdegData
  classical
  let χX : Section1.ClassFunction L := (X : Section1.ClassFunction L)
  let χ1 : Section1.ClassFunction L := (X1 : Section1.ClassFunction L)
  have hXnotinS1 : χX ∉ S1 := by
    intro hXin
    exact hXbarNotin (hS1closed χX hXin)
  have hX1char : Section1.IsCharacter χ1 := by
    exact hsetup.2 ⟨χ1, hS1subset X1.2⟩
  have hX1_ne_bar : χ1 ≠ Section1.conjugateCharacter χ1 := by
    exact (h52a ⟨χ1, hS1subset X1.2⟩).2
  rcases hdegData with ⟨d1, dX, hd1, hdX, hdvd, dS1, hdS1, hineq⟩
  rcases hcoherent with ⟨_hS1_virtual, _hS1_nonempty, Told, hIsoOld, hVirtOld, hAgreeOld⟩
  obtain ⟨a, rfl⟩ := hdvd
  let pair : Finset (Section1.ClassFunction L) :=
    {χX, Section1.conjugateCharacter χX}
  let Snew : Finset (Section1.ClassFunction L) := S1 ∪ pair
  have hXbar_mem_Snew : Section1.conjugateCharacter χX ∈ Snew := by
    simp [Snew, pair]
  have hX_mem_Snew : χX ∈ Snew := by
    simp [Snew, pair]
  have hOld_le_Snew : S1 ⊆ Snew := by
    intro ψ hψ
    simp [Snew, hψ]
  have hX1_in_Snew : χ1 ∈ Snew := hOld_le_Snew X1.2
  let ψ : Section1.ClassFunction L := (a : ℂ) • χ1
  let diffψ : Section1.ClassFunction L := χX - ψ
  let diffX : Section1.ClassFunction L := χX - Section1.conjugateCharacter χX
  have hχX_span_S : integerSpan S χX := integerSpan_of_mem_pf56 S X.2
  have hχ1_span_S1 : integerSpan S1 χ1 := integerSpan_of_mem_pf56 S1 X1.2
  have hψ_span_S1 : integerSpan S1 ψ := by
    exact integerSpan_nsmul_pf56 a hχ1_span_S1
  have hψ_span_S : integerSpan S ψ := integerSpan_mono_pf56 hS1subset hψ_span_S1
  have hdiffψ_span_S : integerSpan S diffψ := by
    exact integerSpan_sub_pf56 hχX_span_S hψ_span_S
  have hχXbar_mem_S : Section1.conjugateCharacter χX ∈ S := (h52a X).1
  have hχXbar_span_S :
      integerSpan S (Section1.conjugateCharacter χX) := integerSpan_of_mem_pf56 S hχXbar_mem_S
  have hdiffX_span_S : integerSpan S diffX := by
    exact integerSpan_sub_pf56 hχX_span_S hχXbar_span_S
  have hψdeg : Section1.degree ψ = (d1 * a : ℂ) := by
    dsimp [ψ]
    have hχ1eval : χ1 1 = (d1 : ℂ) := by
      simpa [Section1.degree_apply] using hd1
    simp [Section1.degree_apply, hχ1eval, mul_comm]
  have hdiffψ_on : Section1.supportedOn diffψ puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf56 diffψ).2
    have hχXdeg : Section1.degree χX = (d1 * a : ℂ) := by
      simpa [χX] using hdX
    dsimp [diffψ]
    rw [Section1.degree_apply]
    have hχX1eval : χX 1 = (d1 * a : ℂ) := by
      simpa [Section1.degree_apply] using hχXdeg
    have hψeval : ψ 1 = (d1 * a : ℂ) := by
      simpa [Section1.degree_apply] using hψdeg
    simp [hχX1eval, hψeval]
  have hdiffX_on : Section1.supportedOn diffX puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf56 diffX).2
    dsimp [diffX]
    have hχXeval : χX 1 = (d1 * a : ℂ) := by
      simpa [Section1.degree_apply] using hdX
    rw [Section1.degree_apply]
    simp [Section1.conjugateCharacter, hχXeval]
  have hdiffψ_memOn : integerSpanOn S puncturedSet diffψ := ⟨hdiffψ_span_S, hdiffψ_on⟩
  have hdiffX_memOn : integerSpanOn S puncturedSet diffX := ⟨hdiffX_span_S, hdiffX_on⟩
  have hsubsetSum_old :
      ∀ Y : S1,
        isSubsetSumOf (R ⟨(Y : Section1.ClassFunction L), hS1subset Y.2⟩)
          (Told (Y : Section1.ClassFunction L)) := by
    intro Y
    let YS : S := ⟨(Y : Section1.ClassFunction L), hS1subset Y.2⟩
    have hYpairIso :
        isCFLinearIsometryOnSpan
          ({(Y : Section1.ClassFunction L),
            Section1.conjugateCharacter (Y : Section1.ClassFunction L)} :
            Finset (Section1.ClassFunction L)) Told := by
      apply isCFLinearIsometryOnSpan_mono_pf56
      · intro ψ hψ
        simp at hψ
        rcases hψ with rfl | rfl
        · exact Y.2
        · exact hS1closed (Y : Section1.ClassFunction L) Y.2
      · exact hIsoOld
    have hYpairVirt :
        mapsIntegerSpanToVirtualCharacters
          ({(Y : Section1.ClassFunction L),
            Section1.conjugateCharacter (Y : Section1.ClassFunction L)} :
            Finset (Section1.ClassFunction L)) Told := by
      apply mapsIntegerSpanToVirtualCharacters_mono_pf56
      · intro ψ hψ
        simp at hψ
        rcases hψ with rfl | rfl
        · exact Y.2
        · exact hS1closed (Y : Section1.ClassFunction L) Y.2
      · exact hVirtOld
    have hYdiffAgree :
        Told ((Y : Section1.ClassFunction L) -
            Section1.conjugateCharacter (Y : Section1.ClassFunction L)) =
          T ((Y : Section1.ClassFunction L) -
            Section1.conjugateCharacter (Y : Section1.ClassFunction L)) := by
      apply hAgreeOld
      refine ⟨?_, ?_⟩
      ·
        let pairY :
            Finset (Section1.ClassFunction L) :=
          {(Y : Section1.ClassFunction L),
            Section1.conjugateCharacter (Y : Section1.ClassFunction L)}
        have hdiff_pairY :
            integerSpan pairY
              ((Y : Section1.ClassFunction L) -
                Section1.conjugateCharacter (Y : Section1.ClassFunction L)) := by
          let yPair : pairY := ⟨(Y : Section1.ClassFunction L), by simp [pairY]⟩
          let ybarPair : pairY :=
            ⟨Section1.conjugateCharacter (Y : Section1.ClassFunction L), by simp [pairY]⟩
          refine ⟨Section1.signedBasisDifference 1 ybarPair yPair, ?_⟩
          ext g
          simpa [yPair, ybarPair, pairY, Section1.signIntToComplex] using
            (congrArg (fun f : Section1.ClassFunction L => f g)
              (Section1.evalCoeff_signedBasisDifference
                (G := L) (J := pairY)
                (mu := fun y : pairY => (y : Section1.ClassFunction L))
                1 ybarPair yPair)).symm
        exact integerSpan_mono_pf56 (by
          intro ψ hψ
          simp [pairY] at hψ
          rcases hψ with rfl | rfl
          · exact Y.2
          · exact hS1closed (Y : Section1.ClassFunction L) Y.2) hdiff_pairY
      ·
        apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf56 _).2
        have hYdeg : (Y : Section1.ClassFunction L) 1 = (dS1 Y : ℂ) := by
          simpa [Section1.degree_apply] using hdS1 Y
        change
          ((Y : Section1.ClassFunction L) -
            Section1.conjugateCharacter (Y : Section1.ClassFunction L)) 1 = 0
        simp [Section1.conjugateCharacter, hYdeg]
    exact theorem_5_5 S T R hsetup h52a h52b h52c h52d h52e YS Told
      hYpairIso hYpairVirt hYdiffAgree
  have hTold_orth_RX :
      ∀ Y : S1, orthogonalToFinset (R X) (Told (Y : Section1.ClassFunction L)) := by
    intro Y
    have hYinS : (Y : Section1.ClassFunction L) ∈ S := hS1subset Y.2
    have hXinS : χX ∈ S := X.2
    have hXbarinS : Section1.conjugateCharacter χX ∈ S := (h52a X).1
    have hYorthX :
        Section1.scalarProduct L (Y : Section1.ClassFunction L) χX = 0 := by
      exact h52c (χ := (Y : Section1.ClassFunction L)) (ψ := χX)
        hYinS hXinS (by
          intro hEq
          exact hXnotinS1 (hEq.symm ▸ Y.2))
    have hYorthXbar :
        Section1.scalarProduct L
            (Y : Section1.ClassFunction L)
            (Section1.conjugateCharacter χX) = 0 := by
      exact h52c (χ := (Y : Section1.ClassFunction L))
        (ψ := Section1.conjugateCharacter χX)
        hYinS hXbarinS (by
          intro hEq
          exact hXbarNotin (hEq.symm ▸ Y.2))
    have horthRYX : orthogonalFinsets (R ⟨(Y : Section1.ClassFunction L), hS1subset Y.2⟩) (R X) := by
      exact h52e X ⟨(Y : Section1.ClassFunction L), hS1subset Y.2⟩ hYorthX hYorthXbar
    exact orthogonalToFinset_of_subsetSum_of_orthogonalFinsets_pf56
      (hsubsetSum_old Y) horthRYX
  have hToldX1_subsetOld :
      isSubsetSumOf (R ⟨χ1, hS1subset X1.2⟩) (Told χ1) := hsubsetSum_old X1
  have hToldX1_orth : orthogonalToFinset (R X) (Told χ1) := hTold_orth_RX X1
  have hToldX1_virt : Theory.Character.IsVirtualCharacter (Told χ1) := hVirtOld χ1 hχ1_span_S1
  have hχXχ1_zero :
      Section1.scalarProduct L χX χ1 = 0 := by
    exact h52c (χ := χX) (ψ := χ1) X.2 (hS1subset X1.2) (by
      intro hEq
      exact hXnotinS1 (hEq.symm ▸ X1.2))
  have hχ1Xbar_zero :
      Section1.scalarProduct L χ1 (Section1.conjugateCharacter χX) = 0 := by
    exact h52c (χ := χ1)
      (ψ := Section1.conjugateCharacter χX)
      (hS1subset X1.2) ((h52a X).1) (by
        intro hEq
        exact hXbarNotin (hEq.symm ▸ X1.2))
  have hXbarχ1_zero :
      Section1.scalarProduct L (Section1.conjugateCharacter χX) χ1 = 0 :=
    scalarProduct_zero_swap_pf56 hχ1Xbar_zero
  have hXψ_zero :
      Section1.scalarProduct L χX ψ = 0 := by
    dsimp [ψ]
    rw [Section1.scalarProduct_smul_right]
    simp [hχXχ1_zero]
  have hXbarψ_zero :
      Section1.scalarProduct L (Section1.conjugateCharacter χX) ψ = 0 := by
    dsimp [ψ]
    rw [Section1.scalarProduct_smul_right]
    simp [hXbarχ1_zero]
  let pairDiff : Finset (Section1.ClassFunction L) := {diffψ, diffX}
  have hpairDiff_gen :
      ∀ φ : Section1.ClassFunction L, φ ∈ pairDiff → integerSpanOn S puncturedSet φ := by
    intro φ hφ
    simp [pairDiff] at hφ
    rcases hφ with rfl | rfl
    · exact hdiffψ_memOn
    · exact hdiffX_memOn
  have hTpairIso :
      isCFLinearIsometryOnSpan pairDiff T := by
    intro φ ψ' hφ hψ'
    exact h52b.1 φ ψ'
      (integerSpanOn_of_generators_pf56 (S := S) (U := pairDiff) (A := puncturedSet)
        hpairDiff_gen hφ)
      (integerSpanOn_of_generators_pf56 (S := S) (U := pairDiff) (A := puncturedSet)
        hpairDiff_gen hψ')
  have hTpairVirt :
      mapsIntegerSpanToVirtualCharacters pairDiff T := by
    intro φ hφ
    exact (h52b.2 φ
      (integerSpanOn_of_generators_pf56 (S := S) (U := pairDiff) (A := puncturedSet)
        hpairDiff_gen hφ)).1
  have hTdiffψ_virt : Theory.Character.IsVirtualCharacter (T diffψ) :=
    (h52b.2 diffψ hdiffψ_memOn).1
  rcases h52d X with ⟨hRX, hTdiffX⟩
  rcases orthogonal_projection_decomposition_pf56 (R := R X) hRX hTdiffψ_virt with
    ⟨Xbig, Y, hXbig_span, hY_orth, hTdiffψ_eq⟩
  have h54 :
      cfNormSq Xbig ≥ cfNormSq χX ∧
        (cfNormSq Y ≥ cfNormSq ψ →
          cfNormSq Xbig = cfNormSq χX ∧
            cfNormSq Y = cfNormSq ψ ∧
              isSubsetSumOf (R X) Xbig) := by
    exact theorem_5_4 S T R hsetup h52a h52b h52c h52d h52e X ψ
      hψ_span_S hXψ_zero hXbarψ_zero T hTpairIso hTpairVirt rfl Xbig Y
      hXbig_span hY_orth hTdiffψ_eq
  have hXbig_ge : cfNormSq Xbig ≥ cfNormSq χX := h54.1
  let μX : R X → Section1.ClassFunction G := fun r => (r : Section1.ClassFunction G)
  have hYXbig_zero :
      Section1.scalarProduct G Y Xbig = 0 := by
    rcases hXbig_span with ⟨v, rfl⟩
    exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf56 μX
      (fun r => hY_orth r.2) v
  have hXbigY_zero :
      Section1.scalarProduct G Xbig Y = 0 :=
    scalarProduct_zero_swap_pf56 hYXbig_zero
  have hsourceNorm :
      cfNormSq diffψ = cfNormSq χX + cfNormSq ψ := by
    dsimp [diffψ]
    exact cfNormSq_sub_eq_add_of_orthogonal_pf56 hXψ_zero
      (scalarProduct_zero_swap_pf56 hXψ_zero)
  have htargetNorm :
      cfNormSq (Xbig - Y) = cfNormSq Xbig + cfNormSq Y := by
    exact cfNormSq_sub_eq_add_of_orthogonal_pf56 hXbigY_zero hYXbig_zero
  have hdiffψ_norm :
      cfNormSq (T diffψ) = cfNormSq diffψ := by
    have hIsoNorm := h52b.1 diffψ diffψ hdiffψ_memOn hdiffψ_memOn
    simpa [cfNormSq] using congrArg Complex.re hIsoNorm
  have hsumNorm :
      cfNormSq χX + cfNormSq ψ = cfNormSq Xbig + cfNormSq Y := by
    calc
      cfNormSq χX + cfNormSq ψ = cfNormSq diffψ := hsourceNorm.symm
      _ = cfNormSq (T diffψ) := hdiffψ_norm.symm
      _ = cfNormSq (Xbig - Y) := by rw [hTdiffψ_eq]
      _ = cfNormSq Xbig + cfNormSq Y := htargetNorm
  have hY_le : cfNormSq Y ≤ cfNormSq ψ := by
    linarith
  have hToldX1_norm :
      cfNormSq (Told χ1) = cfNormSq χ1 := by
    have hIsoNorm := hIsoOld χ1 χ1 hχ1_span_S1 hχ1_span_S1
    simpa [cfNormSq] using congrArg Complex.re hIsoNorm
  have hχ1_self_int :
      ∃ n1 : ℤ, Section1.scalarProduct L χ1 χ1 = (n1 : ℂ) := by
    rcases Section3.scalarProduct_isVirtualCharacter_eq_int hToldX1_virt hToldX1_virt with
      ⟨n1, hn1⟩
    refine ⟨n1, ?_⟩
    calc
      Section1.scalarProduct L χ1 χ1 =
          Section1.scalarProduct G (Told χ1) (Told χ1) := by
            symm
            exact hIsoOld χ1 χ1 hχ1_span_S1 hχ1_span_S1
      _ = (n1 : ℂ) := hn1
  have hχ1_cfNorm_int :
      ∃ n1 : ℤ, cfNormSq χ1 = (n1 : ℝ) := by
    rcases hχ1_self_int with ⟨n1, hn1⟩
    refine ⟨n1, ?_⟩
    unfold cfNormSq
    rw [hn1]
    simp
  have hd1_ne_zero : (d1 : ℂ) ≠ 0 := by
    intro hd10
    have hdeg0 : Section1.degree χ1 = 0 := hd1.trans hd10
    have hχ1_zero : χ1 = 0 := character_eq_zero_of_degree_zero_pf56 hX1char hdeg0
    have hbar_zero : Section1.conjugateCharacter (0 : Section1.ClassFunction L) = 0 := by
      ext g
      simp [Section1.conjugateCharacter]
    have hχ1_bar : χ1 = Section1.conjugateCharacter χ1 := by
      calc
        χ1 = 0 := hχ1_zero
        _ = Section1.conjugateCharacter (0 : Section1.ClassFunction L) := hbar_zero.symm
        _ = Section1.conjugateCharacter χ1 := by simp [hχ1_zero]
    exact hX1_ne_bar hχ1_bar
  have hTdiffψ_toldX1_int :
      ∃ m : ℤ, Section1.scalarProduct G (T diffψ) (Told χ1) = (m : ℂ) := by
    exact Section3.scalarProduct_isVirtualCharacter_eq_int hTdiffψ_virt hToldX1_virt
  let n1 : ℤ := Classical.choose hχ1_cfNorm_int
  have hn1 : cfNormSq χ1 = (n1 : ℝ) := Classical.choose_spec hχ1_cfNorm_int
  have hψ_norm :
      cfNormSq ψ = (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) := by
    dsimp [ψ]
    calc
      cfNormSq ((a : ℂ) • χ1) = (a : ℝ) ^ (2 : ℕ) * cfNormSq χ1 := by
        unfold cfNormSq
        rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
        simp [pow_two, mul_assoc, mul_left_comm]
      _ = (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) := by rw [hn1]
  rcases hTdiffψ_toldX1_int with ⟨m, hm⟩
  have hToldX1_Xbig_zero :
      Section1.scalarProduct G (Told χ1) Xbig = 0 := by
    rcases hXbig_span with ⟨v, rfl⟩
    exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf56 μX
      (fun r => hToldX1_orth r.2) v
  have hXbig_toldX1_zero :
      Section1.scalarProduct G Xbig (Told χ1) = 0 :=
    scalarProduct_zero_swap_pf56 hToldX1_Xbig_zero
  have hY_eq :
      Xbig - T diffψ = Y := by
    ext g
    have h : T diffψ g = Xbig g - Y g := by
      simpa using congrArg (fun f : Section1.ClassFunction G => f g) hTdiffψ_eq
    calc
      Xbig g - T diffψ g = Xbig g - (Xbig g - Y g) := by rw [h]
      _ = Y g := by ring
  have hY_toldX1 :
      Section1.scalarProduct G Y (Told χ1) = (-m : ℂ) := by
    rw [← hY_eq, scalarProduct_sub_left_pf56]
    simp [hXbig_toldX1_zero, hm]
  let A : ℤ := (a : ℤ) * n1 + m
  have hconj_zero_L :
      Section1.conjugateCharacter (0 : Section1.ClassFunction L) = 0 := by
    ext g
    simp [Section1.conjugateCharacter]
  have hχ1_self :
      Section1.scalarProduct L χ1 χ1 = (n1 : ℂ) := by
    rcases hχ1_self_int with ⟨n1', hn1'⟩
    have hn1'real : cfNormSq χ1 = (n1' : ℝ) := by
      unfold cfNormSq
      rw [hn1']
      simp
    have hn1'eq_real : (n1' : ℝ) = (n1 : ℝ) := by
      rw [← hn1'real, hn1]
    have hn1'eq : n1' = n1 := by
      exact_mod_cast hn1'eq_real
    simpa [hn1'eq] using hn1'
  have hχ1_cfNorm_ne_zero : cfNormSq χ1 ≠ 0 := by
    intro h0
    have hχ1_zero : χ1 = 0 := cfNormSq_eq_zero_pf56 h0
    have hχ1_bar : χ1 = Section1.conjugateCharacter χ1 := by
      calc
        χ1 = 0 := hχ1_zero
        _ = Section1.conjugateCharacter (0 : Section1.ClassFunction L) := hconj_zero_L.symm
        _ = Section1.conjugateCharacter χ1 := by simp [hχ1_zero]
    exact hX1_ne_bar hχ1_bar
  have hn1_ne_zero : (n1 : ℝ) ≠ 0 := by
    rw [← hn1]
    exact hχ1_cfNorm_ne_zero
  have hd1_nat_ne_zero : d1 ≠ 0 := by
    intro hd10
    exact hd1_ne_zero (by exact_mod_cast hd10)
  have hd1_real_ne_zero : (d1 : ℝ) ≠ 0 := by
    exact_mod_cast hd1_nat_ne_zero
  have hX1_deg_eq : dS1 X1 = d1 := by
    have hcast : (dS1 X1 : ℂ) = (d1 : ℂ) := by
      rw [← hd1, hdS1 X1]
    exact_mod_cast hcast
  let μOld : S1 → Section1.ClassFunction G := fun Y0 => Told (Y0 : Section1.ClassFunction L)
  have hμOld_orth :
      ∀ Y1 Y2 : S1,
        Y1 ≠ Y2 →
          Section1.scalarProduct G (μOld Y1) (μOld Y2) = 0 := by
    intro Y1 Y2 hne
    have hsrc :
        Section1.scalarProduct L
            (Y1 : Section1.ClassFunction L)
            (Y2 : Section1.ClassFunction L) = 0 := by
      exact h52c (χ := (Y1 : Section1.ClassFunction L))
        (ψ := (Y2 : Section1.ClassFunction L))
        (hS1subset Y1.2) (hS1subset Y2.2) (by
          intro hEq
          exact hne (Subtype.ext hEq))
    calc
      Section1.scalarProduct G (μOld Y1) (μOld Y2) =
          Section1.scalarProduct L
            (Y1 : Section1.ClassFunction L)
            (Y2 : Section1.ClassFunction L) := by
              exact hIsoOld _ _
                (integerSpan_of_mem_pf56 S1 Y1.2)
                (integerSpan_of_mem_pf56 S1 Y2.2)
      _ = 0 := hsrc
  have hμOld_self :
      ∀ Y0 : S1,
        Section1.scalarProduct G (μOld Y0) (μOld Y0) =
          (cfNormSq (Y0 : Section1.ClassFunction L) : ℂ) := by
    intro Y0
    have hY0char : Section1.IsCharacter (Y0 : Section1.ClassFunction L) := by
      exact hsetup.2 ⟨(Y0 : Section1.ClassFunction L), hS1subset Y0.2⟩
    rcases Section1.scalarProduct_character_character_eq_nat
        (Y0 : Section1.ClassFunction L) (Y0 : Section1.ClassFunction L)
        hY0char hY0char with ⟨nY0, hnY0⟩
    have hnY0real : cfNormSq (Y0 : Section1.ClassFunction L) = (nY0 : ℝ) := by
      unfold cfNormSq
      rw [hnY0]
      simp
    calc
      Section1.scalarProduct G (μOld Y0) (μOld Y0) =
          Section1.scalarProduct L
            (Y0 : Section1.ClassFunction L)
            (Y0 : Section1.ClassFunction L) := by
              exact hIsoOld _ _
                (integerSpan_of_mem_pf56 S1 Y0.2)
                (integerSpan_of_mem_pf56 S1 Y0.2)
      _ = (nY0 : ℂ) := hnY0
      _ = (cfNormSq (Y0 : Section1.ClassFunction L) : ℂ) := by
            simp [hnY0real]
  have hμOld_norm_ne_zero :
      ∀ Y0 : S1, cfNormSq (Y0 : Section1.ClassFunction L) ≠ 0 := by
    intro Y0 h0
    have hY0_zero : (Y0 : Section1.ClassFunction L) = 0 := cfNormSq_eq_zero_pf56 h0
    have hY0_bar :
        (Y0 : Section1.ClassFunction L) =
          Section1.conjugateCharacter (Y0 : Section1.ClassFunction L) := by
      calc
        (Y0 : Section1.ClassFunction L) = 0 := hY0_zero
        _ = Section1.conjugateCharacter (0 : Section1.ClassFunction L) := hconj_zero_L.symm
        _ = Section1.conjugateCharacter (Y0 : Section1.ClassFunction L) := by
              simp [hY0_zero]
    exact (h52a ⟨(Y0 : Section1.ClassFunction L), hS1subset Y0.2⟩).2 hY0_bar
  have hY_told_old :
      ∀ Y0 : S1, Y0 ≠ X1 →
        Section1.scalarProduct G Y (μOld Y0) =
          (-((A : ℂ) * (dS1 Y0 : ℂ))) / (d1 : ℂ) := by
    intro Y0 hY0X1
    let η : Section1.ClassFunction L :=
      (d1 : ℂ) • (Y0 : Section1.ClassFunction L) - (dS1 Y0 : ℂ) • χ1
    have hη_span_S1 : integerSpan S1 η := by
      dsimp [η]
      exact integerSpan_sub_pf56
        (integerSpan_nsmul_pf56 d1 (integerSpan_of_mem_pf56 S1 Y0.2))
        (integerSpan_nsmul_pf56 (dS1 Y0) hχ1_span_S1)
    have hη_on : Section1.supportedOn η puncturedSet := by
      apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf56 η).2
      change η 1 = 0
      have hY0eval : (Y0 : Section1.ClassFunction L) 1 = (dS1 Y0 : ℂ) := by
        simpa [Section1.degree_apply] using hdS1 Y0
      have hχ1eval : χ1 1 = (d1 : ℂ) := by
        simpa [Section1.degree_apply] using hd1
      simp [η, hY0eval, hχ1eval, mul_comm]
    have hη_memOn_S : integerSpanOn S puncturedSet η := by
      exact ⟨integerSpan_mono_pf56 hS1subset hη_span_S1, hη_on⟩
    have hη_agree : Told η = T η := hAgreeOld η ⟨hη_span_S1, hη_on⟩
    have hχXY0_zero :
        Section1.scalarProduct L χX (Y0 : Section1.ClassFunction L) = 0 := by
      exact h52c (χ := χX) (ψ := (Y0 : Section1.ClassFunction L))
        X.2 (hS1subset Y0.2) (by
          intro hEq
          exact hXnotinS1 (hEq.symm ▸ Y0.2))
    have hχ1Y0_zero :
        Section1.scalarProduct L χ1 (Y0 : Section1.ClassFunction L) = 0 := by
      exact h52c (χ := χ1) (ψ := (Y0 : Section1.ClassFunction L))
        (hS1subset X1.2) (hS1subset Y0.2) (by
          intro hEq
          exact hY0X1 (Subtype.ext hEq.symm))
    have hχX_eta_zero :
        Section1.scalarProduct L χX η = 0 := by
      dsimp [η]
      rw [scalarProduct_sub_right_pf56, Section1.scalarProduct_smul_right,
        Section1.scalarProduct_smul_right]
      simp [hχXY0_zero, hχXχ1_zero]
    have hχ1_eta :
        Section1.scalarProduct L χ1 η =
          (-(((dS1 Y0 : ℤ) * n1 : ℤ) : ℂ)) := by
      dsimp [η]
      rw [scalarProduct_sub_right_pf56, Section1.scalarProduct_smul_right,
        Section1.scalarProduct_smul_right]
      simp [hχ1Y0_zero, hχ1_self, Int.cast_mul]
    have hsource :
        Section1.scalarProduct L diffψ η =
          ((((a : ℤ) * n1 * (dS1 Y0 : ℤ)) : ℤ) : ℂ) := by
      dsimp [diffψ]
      rw [scalarProduct_sub_left_pf56]
      have hpsi_eta :
          Section1.scalarProduct L ψ η =
            (-((((a : ℤ) * n1 * (dS1 Y0 : ℤ)) : ℤ) : ℂ)) := by
        dsimp [ψ]
        rw [Section1.scalarProduct_smul_left]
        simp [hχ1_eta, Int.cast_mul, mul_left_comm, mul_comm]
      simp [hχX_eta_zero, hpsi_eta]
    have hμOld_Xbig_zero :
        Section1.scalarProduct G (μOld Y0) Xbig = 0 := by
      rcases hXbig_span with ⟨v, rfl⟩
      exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf56 μX
        (fun r => hTold_orth_RX Y0 r.2) v
    have hXbig_μOld_zero :
        Section1.scalarProduct G Xbig (μOld Y0) = 0 :=
      scalarProduct_zero_swap_pf56 hμOld_Xbig_zero
    have htarget :
        Section1.scalarProduct G (T diffψ) (Told η) =
          ((((a : ℤ) * n1 * (dS1 Y0 : ℤ)) : ℤ) : ℂ) := by
      calc
        Section1.scalarProduct G (T diffψ) (Told η) =
            Section1.scalarProduct G (T diffψ) (T η) := by rw [hη_agree]
        _ = Section1.scalarProduct L diffψ η :=
            h52b.1 diffψ η hdiffψ_memOn hη_memOn_S
        _ = ((((a : ℤ) * n1 * (dS1 Y0 : ℤ)) : ℤ) : ℂ) := hsource
    have hmain :
        (d1 : ℂ) * Section1.scalarProduct G Y (μOld Y0) =
          -((A : ℂ) * (dS1 Y0 : ℂ)) := by
      have hTold_eta :
          Told η = (d1 : ℂ) • μOld Y0 - (dS1 Y0 : ℂ) • Told χ1 := by
        dsimp [η, μOld]
        simp
      have htmp :
          Section1.scalarProduct G (T diffψ) (Told η) =
            -(d1 : ℂ) * Section1.scalarProduct G Y (μOld Y0) +
              (dS1 Y0 : ℂ) * Section1.scalarProduct G Y (Told χ1) := by
        rw [hTdiffψ_eq]
        rw [hTold_eta, scalarProduct_sub_right_pf56, Section1.scalarProduct_smul_right,
          Section1.scalarProduct_smul_right, scalarProduct_sub_left_pf56,
          scalarProduct_sub_left_pf56]
        simp [sub_eq_add_neg, hXbig_μOld_zero, hXbig_toldX1_zero, hY_toldX1,
          mul_comm]
      rw [hY_toldX1] at htmp
      rw [htarget] at htmp
      have htmp' :
          ((((a : ℤ) * n1 * (dS1 Y0 : ℤ)) : ℤ) : ℂ) =
            -((d1 : ℂ) * Section1.scalarProduct G Y (μOld Y0)) -
              (dS1 Y0 : ℂ) * (m : ℂ) := by
        simpa [sub_eq_add_neg, add_assoc, mul_assoc, mul_left_comm, mul_comm] using htmp
      have htmp'' :
          ((a : ℂ) * ((dS1 Y0 : ℂ) * (n1 : ℂ))) =
            -((d1 : ℂ) * Section1.scalarProduct G Y (μOld Y0)) -
              (m : ℂ) * (dS1 Y0 : ℂ) := by
        simpa [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm] using htmp'
      apply (eq_neg_iff_add_eq_zero).2
      have hsum := congrArg
        (fun z : ℂ =>
          z + (d1 : ℂ) * Section1.scalarProduct G Y (μOld Y0) +
            (m : ℂ) * (dS1 Y0 : ℂ)) htmp''
      simpa [A, add_mul, mul_add, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hsum
    apply (eq_div_iff hd1_ne_zero).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  let wCorr : S1 → ℝ := fun Y0 =>
    -((A : ℝ) * (dS1 Y0 : ℝ)) /
      ((d1 : ℝ) * cfNormSq (Y0 : Section1.ClassFunction L))
  let P : Section1.ClassFunction G :=
    Section1.weightedFamilySum (fun Y0 => (wCorr Y0 : ℂ)) μOld
  have hP_told :
      ∀ Y0 : S1,
        Section1.scalarProduct G P (μOld Y0) =
          (-((A : ℂ) * (dS1 Y0 : ℂ))) / (d1 : ℂ) := by
    intro Y0
    have hcoeff :=
      scalarProduct_weightedFamilySum_left_orthogonal_real_pf56
        wCorr μOld
        (fun Y1 => cfNormSq (Y1 : Section1.ClassFunction L))
        hμOld_orth hμOld_self Y0
    calc
      Section1.scalarProduct G P (μOld Y0) =
          (((wCorr Y0 * cfNormSq (Y0 : Section1.ClassFunction L) : ℝ)) : ℂ) := by
            dsimp [P]
            simpa using hcoeff
      _ = (-((A : ℂ) * (dS1 Y0 : ℂ))) / (d1 : ℂ) := by
            have hreal :
                wCorr Y0 * cfNormSq (Y0 : Section1.ClassFunction L) =
                  -((A : ℝ) * (dS1 Y0 : ℝ)) / (d1 : ℝ) := by
              dsimp [wCorr]
              field_simp [hd1_real_ne_zero, hμOld_norm_ne_zero Y0]
            simpa using congrArg (fun t : ℝ => (t : ℂ)) hreal
  have hdS1X1C : (dS1 X1 : ℂ) = (d1 : ℂ) := by
    exact_mod_cast hX1_deg_eq
  have hP_toldX1 :
      Section1.scalarProduct G P (μOld X1) = -(A : ℂ) := by
    calc
      Section1.scalarProduct G P (μOld X1) =
          (-((A : ℂ) * (dS1 X1 : ℂ))) / (d1 : ℂ) := hP_told X1
      _ = (-((A : ℂ) * (d1 : ℂ))) / (d1 : ℂ) := by rw [hdS1X1C]
      _ = -(A : ℂ) := by
            field_simp [hd1_ne_zero]
  let W : Section1.ClassFunction G := (a : ℂ) • μOld X1 + P
  have hW_told :
      ∀ Y0 : S1,
        Section1.scalarProduct G W (μOld Y0) =
          Section1.scalarProduct G Y (μOld Y0) := by
    intro Y0
    by_cases hY0X1 : Y0 = X1
    · subst Y0
      calc
        Section1.scalarProduct G W (μOld X1) =
            Section1.scalarProduct G ((a : ℂ) • μOld X1) (μOld X1) +
              Section1.scalarProduct G P (μOld X1) := by
                dsimp [W]
                rw [Section1.scalarProduct_add_left]
        _ = (((a : ℤ) * n1 : ℤ) : ℂ) - (A : ℂ) := by
              have hselfX1 :
                  Section1.scalarProduct G (μOld X1) (μOld X1) = (n1 : ℂ) := by
                simpa [χ1, hn1] using hμOld_self X1
              rw [Section1.scalarProduct_smul_left]
              rw [hselfX1, hP_toldX1]
              simp [Int.cast_mul, sub_eq_add_neg]
        _ = (-m : ℂ) := by
              have hInt : ((a : ℤ) * n1 : ℤ) - A = -m := by
                dsimp [A]
                omega
              exact_mod_cast hInt
        _ = Section1.scalarProduct G Y (μOld X1) := hY_toldX1.symm
    · have hX1Y0 :
          Section1.scalarProduct G ((a : ℂ) • μOld X1) (μOld Y0) = 0 := by
        rw [Section1.scalarProduct_smul_left]
        have horth : Section1.scalarProduct G (μOld X1) (μOld Y0) = 0 := by
          exact hμOld_orth X1 Y0 (by
            intro hEq
            exact hY0X1 hEq.symm)
        simp [horth]
      calc
        Section1.scalarProduct G W (μOld Y0) =
            Section1.scalarProduct G ((a : ℂ) • μOld X1) (μOld Y0) +
              Section1.scalarProduct G P (μOld Y0) := by
                dsimp [W]
                rw [Section1.scalarProduct_add_left]
        _ = Section1.scalarProduct G Y (μOld Y0) := by
              rw [hX1Y0, zero_add, hP_told Y0, hY_told_old Y0 hY0X1]
  let Zold : Section1.ClassFunction G := Y - W
  have hZold_orth :
      ∀ Y0 : S1,
        Section1.scalarProduct G Zold (μOld Y0) = 0 := by
    intro Y0
    dsimp [Zold]
    rw [scalarProduct_sub_left_pf56, hW_told Y0]
    simp
  have hZold_P_zero :
      Section1.scalarProduct G Zold P = 0 := by
    dsimp [P]
    rw [Section1.scalarProduct_weightedFamilySum_right]
    simp_rw [hZold_orth]
    simp
  have hZold_W_zero :
      Section1.scalarProduct G Zold W = 0 := by
    dsimp [W]
    rw [scalarProduct_add_right_pf56, Section1.scalarProduct_smul_right]
    simp [hZold_orth X1, hZold_P_zero]
  have hW_Zold_zero :
      Section1.scalarProduct G W Zold = 0 :=
    scalarProduct_zero_swap_pf56 hZold_W_zero
  have hY_decomp :
      Y = W + Zold := by
    simp [Zold, sub_eq_add_neg, add_left_comm]
  have hW_le_Y :
      cfNormSq W ≤ cfNormSq Y := by
    have hYnorm :
        cfNormSq Y = cfNormSq W + cfNormSq Zold := by
      rw [hY_decomp]
      exact cfNormSq_add_eq_add_of_orthogonal_pf56 hW_Zold_zero hZold_W_zero
    have hZnonneg : 0 ≤ cfNormSq Zold := cfNormSq_nonneg_pf56 Zold
    linarith
  let u : Finset S1 := @Finset.univ S1 (Finset.Subtype.fintype S1)
  let sumDegNorm : ℝ :=
    Finset.sum u fun Y0 =>
      (((dS1 Y0 : ℝ) ^ (2 : ℕ)) / cfNormSq (Y0 : Section1.ClassFunction L))
  have hP_norm0 :=
    cfNormSq_weightedFamilySum_orthogonal_real_pf56
      wCorr μOld
      (fun Y0 => cfNormSq (Y0 : Section1.ClassFunction L))
      hμOld_orth hμOld_self
  have hu :
      (@Finset.univ S1 (Fintype.ofFinite S1)) = u := by
    ext Y0
    simp [u]
  have hP_norm0' :
      cfNormSq P =
        Finset.sum u
          (fun Y0 => (wCorr Y0) ^ (2 : ℕ) * cfNormSq (Y0 : Section1.ClassFunction L)) := by
    simpa [u, hu] using hP_norm0
  have hP_norm :
      cfNormSq P = ((A : ℝ) ^ (2 : ℕ) / (d1 : ℝ) ^ (2 : ℕ)) * sumDegNorm := by
    rw [hP_norm0']
    calc
      Finset.sum u (fun Y0 => (wCorr Y0) ^ (2 : ℕ) * cfNormSq (Y0 : Section1.ClassFunction L)) =
          Finset.sum u (fun Y0 =>
            (((A : ℝ) ^ (2 : ℕ) / (d1 : ℝ) ^ (2 : ℕ)) *
              (((dS1 Y0 : ℝ) ^ (2 : ℕ)) /
                cfNormSq (Y0 : Section1.ClassFunction L)))) := by
            refine Finset.sum_congr rfl ?_
            intro Y0 _hY0
            have hnorm_ne :
                cfNormSq (Y0 : Section1.ClassFunction L) ≠ 0 := hμOld_norm_ne_zero Y0
            dsimp [wCorr]
            field_simp [hd1_real_ne_zero, hnorm_ne]
      _ = ((A : ℝ) ^ (2 : ℕ) / (d1 : ℝ) ^ (2 : ℕ)) * sumDegNorm := by
            simp [sumDegNorm, Finset.mul_sum]
  have hμOldX1_P :
      Section1.scalarProduct G (μOld X1) P = -(A : ℂ) := by
    have hstar := congrArg star hP_toldX1
    simpa [Section1.scalarProduct_star_swap] using hstar
  have hW_norm :
      cfNormSq W =
        (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) + cfNormSq P - 2 * (a : ℝ) * (A : ℝ) := by
    have hselfX1 :
        Section1.scalarProduct G (μOld X1) (μOld X1) = (n1 : ℂ) := by
      simpa [χ1, hn1] using hμOld_self X1
    unfold cfNormSq
    dsimp [W]
    rw [Section1.scalarProduct_add_left, scalarProduct_add_right_pf56,
      scalarProduct_add_right_pf56]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, hselfX1,
      hP_toldX1, hμOldX1_P]
    simp [pow_two, sub_eq_add_neg, mul_assoc, mul_comm]
    nlinarith [hn1]
  have hY_upper :
      cfNormSq Y ≤ (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) := by
    simpa [hψ_norm] using hY_le
  have hsumDegNorm_gt :
      2 * (a : ℝ) * (d1 : ℝ) ^ (2 : ℕ) < sumDegNorm := by
    change 2 * (a : ℝ) * (d1 : ℝ) ^ (2 : ℕ) <
      Finset.sum u (fun Y0 =>
        ((dS1 Y0 : ℝ) ^ (2 : ℕ)) / cfNormSq (Y0 : Section1.ClassFunction L))
    rw [show u = S1.attach by rfl]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hineq
  have hsumDegNorm_pos :
      0 < sumDegNorm := by
    have hleft_nonneg : 0 ≤ 2 * (a : ℝ) * (d1 : ℝ) ^ (2 : ℕ) := by
      positivity
    linarith [hsumDegNorm_gt, hleft_nonneg]
  have hAineq :
      ((A : ℝ) ^ (2 : ℕ) / (d1 : ℝ) ^ (2 : ℕ)) * sumDegNorm -
        2 * (a : ℝ) * (A : ℝ) ≤ 0 := by
    let t : ℝ :=
      ((A : ℝ) ^ (2 : ℕ) / (d1 : ℝ) ^ (2 : ℕ)) * sumDegNorm -
        2 * (a : ℝ) * (A : ℝ)
    have hW_bound :
        (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) + t ≤
          (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) := by
      calc
        (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) + t
            =
          (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) +
            (((A : ℝ) ^ (2 : ℕ) / (d1 : ℝ) ^ (2 : ℕ)) * sumDegNorm) -
            2 * (a : ℝ) * (A : ℝ) := by
              dsimp [t]
              ring
        _ = cfNormSq W := by rw [hW_norm, hP_norm]
        _ ≤ cfNormSq Y := hW_le_Y
        _ ≤ (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) := hY_upper
    have ht_nonpos : t ≤ 0 := by
      linarith
    change t ≤ 0
    exact ht_nonpos
  have hd1_sq_pos : 0 < (d1 : ℝ) ^ (2 : ℕ) := by
    positivity
  have hA_zero : A = 0 := by
    exact int_eq_zero_of_quadratic_bound_pf56 a d1 A sumDegNorm
      hd1_sq_pos hsumDegNorm_gt hsumDegNorm_pos hAineq
  have hP_zeroNorm : cfNormSq P = 0 := by
    rw [hP_norm, hA_zero]
    simp
  have hP_zero : P = 0 := cfNormSq_eq_zero_pf56 hP_zeroNorm
  have hZold_zeroNorm : cfNormSq Zold = 0 := by
    have hYnorm :
        cfNormSq Y = cfNormSq W + cfNormSq Zold := by
      rw [hY_decomp]
      exact cfNormSq_add_eq_add_of_orthogonal_pf56 hW_Zold_zero hZold_W_zero
    have hW_eq :
        cfNormSq W = (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) := by
      rw [hW_norm, hP_zeroNorm, hA_zero]
      simp
    have hsum_le :
        (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) + cfNormSq Zold ≤
          (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) := by
      calc
        (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) + cfNormSq Zold = cfNormSq Y := by
          rw [hYnorm, hW_eq]
        _ ≤ (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) := hY_upper
    have hZold_nonpos : cfNormSq Zold ≤ 0 := by
      linarith
    have hZold_nonneg : 0 ≤ cfNormSq Zold := cfNormSq_nonneg_pf56 Zold
    linarith
  have hZold_zero : Zold = 0 := cfNormSq_eq_zero_pf56 hZold_zeroNorm
  have hY_eq_W : Y = W := by
    dsimp [Zold] at hZold_zero
    exact sub_eq_zero.mp hZold_zero
  have hY_eq_aToldX1 :
      Y = (a : ℂ) • Told χ1 := by
    calc
      Y = W := hY_eq_W
      _ = (a : ℂ) • Told χ1 := by
            dsimp [W, μOld]
            simp [χ1, hP_zero]
  have hY_eqψnorm :
      cfNormSq Y = cfNormSq ψ := by
    rw [hY_eq_aToldX1, hψ_norm]
    calc
      cfNormSq ((a : ℂ) • Told χ1) = (a : ℝ) ^ (2 : ℕ) * cfNormSq (Told χ1) := by
        simpa using cfNormSq_natCast_smul_pf56 a (Told χ1)
      _ = (a : ℝ) ^ (2 : ℕ) * (n1 : ℝ) := by rw [hToldX1_norm, hn1]
  have hY_ge : cfNormSq Y ≥ cfNormSq ψ := by
    linarith [hY_eqψnorm]
  have h54eq :
      cfNormSq Xbig = cfNormSq χX ∧
        cfNormSq Y = cfNormSq ψ ∧
          isSubsetSumOf (R X) Xbig := h54.2 hY_ge
  rcases h54eq with ⟨hXbig_norm_eq, _hYeq, hsubsetXbig⟩
  have hY_eq_Toldψ : Y = Told ψ := by
    calc
      Y = (a : ℂ) • Told χ1 := hY_eq_aToldX1
      _ = Told ψ := by
            dsimp [ψ]
            simp
  rcases hsubsetXbig with ⟨E, hEsub, hXbig_subset⟩
  let Ecomp : Finset (Section1.ClassFunction G) := (R X) \ E
  have hEcomp_subset : Ecomp ⊆ R X := Finset.sdiff_subset
  let Xbarimg : Section1.ClassFunction G := Xbig - T diffX
  have hsumEcomp :
      Finset.sum (R X) (fun φ => φ) =
        Finset.sum E (fun φ => φ) + Finset.sum Ecomp (fun φ => φ) := by
    simpa [Ecomp, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_sdiff hEsub (f := fun φ : Section1.ClassFunction G => φ)).symm
  have hXbarimg_eq_neg_sum :
      Xbarimg = -Finset.sum Ecomp (fun φ => φ) := by
    calc
      Xbarimg = Xbig - T diffX := rfl
      _ = Finset.sum E (fun φ => φ) - Finset.sum (R X) (fun φ => φ) := by
            rw [hXbig_subset, hTdiffX]
      _ = -Finset.sum Ecomp (fun φ => φ) := by
            rw [hsumEcomp]
            abel
  let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
  have hχXchar : Section1.IsCharacter χX := hsetup.2 X
  have hχXbar_char : Section1.IsCharacter χXbar := by
    exact hsetup.2 ⟨χXbar, (h52a X).1⟩
  have hχX_self :
      Section1.scalarProduct L χX χX = (cfNormSq χX : ℂ) :=
    scalarProduct_self_eq_cfNormSq_of_character_pf56 hχXchar
  have hχXbar_self :
      Section1.scalarProduct L χXbar χXbar = (cfNormSq χXbar : ℂ) := by
    dsimp [χXbar]
    exact scalarProduct_self_eq_cfNormSq_of_character_pf56 hχXbar_char
  have hχXbar_zero_L :
      Section1.scalarProduct L χXbar χX = 0 := by
    exact h52c (χ := χXbar) (ψ := χX) ((h52a X).1) X.2 (by
      intro hEq
      exact (h52a X).2 (by simpa [χXbar] using hEq.symm))
  have hχX_zero_Xbar :
      Section1.scalarProduct L χX χXbar = 0 := by
    exact h52c (χ := χX) (ψ := χXbar) X.2 ((h52a X).1) (by
      intro hEq
      exact (h52a X).2 (by simpa [χXbar] using hEq))
  have hχX_cfNorm_ne_zero : cfNormSq χX ≠ 0 := by
    intro h0
    have hχX_zero : χX = 0 := cfNormSq_eq_zero_pf56 h0
    have hχX_bar : χX = Section1.conjugateCharacter χX := by
      calc
        χX = 0 := hχX_zero
        _ = Section1.conjugateCharacter (0 : Section1.ClassFunction L) := by
              ext g
              simp [Section1.conjugateCharacter]
        _ = Section1.conjugateCharacter χX := by simp [hχX_zero]
    exact (h52a X).2 hχX_bar
  have hχXbar_cfNorm_ne_zero : cfNormSq χXbar ≠ 0 := by
    intro h0
    have hχXbar_zero : χXbar = 0 := cfNormSq_eq_zero_pf56 h0
    have hχXbar_bar : χXbar = Section1.conjugateCharacter χXbar := by
      calc
        χXbar = 0 := hχXbar_zero
        _ = Section1.conjugateCharacter (0 : Section1.ClassFunction L) := by
              ext g
              simp [Section1.conjugateCharacter]
        _ = Section1.conjugateCharacter χXbar := by
              simp [χXbar, hχXbar_zero]
    exact (h52a ⟨χXbar, (h52a X).1⟩).2 hχXbar_bar
  let coeffX : Section1.ClassFunction L →ₗ[ℂ] ℂ :=
    { toFun := fun φ => (Section1.scalarProduct L χX χX)⁻¹ * Section1.scalarProduct L φ χX
      map_add' := by
        intro φ ψ'
        rw [Section1.scalarProduct_add_left]
        simp [mul_add]
      map_smul' := by
        intro z φ
        rw [Section1.scalarProduct_smul_left]
        simp [smul_eq_mul, mul_left_comm] }
  let coeffXbar : Section1.ClassFunction L →ₗ[ℂ] ℂ :=
    { toFun := fun φ => (Section1.scalarProduct L χXbar χXbar)⁻¹ * Section1.scalarProduct L φ χXbar
      map_add' := by
        intro φ ψ'
        rw [Section1.scalarProduct_add_left]
        simp [mul_add]
      map_smul' := by
        intro z φ
        rw [Section1.scalarProduct_smul_left]
        simp [smul_eq_mul, mul_left_comm] }
  let Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G :=
    Told +
      coeffX.smulRight (Xbig - Told χX) +
        coeffXbar.smulRight (Xbarimg - Told χXbar)
  have hcoeffX_old :
      ∀ Y0 : S1, coeffX (Y0 : Section1.ClassFunction L) = 0 := by
    intro Y0
    dsimp [coeffX]
    have horth :
        Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χX = 0 := by
      exact h52c (χ := (Y0 : Section1.ClassFunction L)) (ψ := χX)
        (hS1subset Y0.2) X.2 (by
          intro hEq
          exact hXnotinS1 (hEq ▸ Y0.2))
    simp [horth]
  have hcoeffXbar_old :
      ∀ Y0 : S1, coeffXbar (Y0 : Section1.ClassFunction L) = 0 := by
    intro Y0
    dsimp [coeffXbar]
    have horth :
        Section1.scalarProduct L (Y0 : Section1.ClassFunction L) χXbar = 0 := by
      exact h52c (χ := (Y0 : Section1.ClassFunction L)) (ψ := χXbar)
        (hS1subset Y0.2) ((h52a X).1) (by
          intro hEq
          have hmem : χXbar ∈ S1 := hEq ▸ Y0.2
          exact hXbarNotin (by simpa [χXbar] using hmem))
    simp [horth]
  have hTnew_old :
      ∀ Y0 : S1, Tnew (Y0 : Section1.ClassFunction L) = Told (Y0 : Section1.ClassFunction L) := by
    intro Y0
    dsimp [Tnew]
    simp [hcoeffX_old Y0, hcoeffXbar_old Y0]
  have hcoeffX_self :
      coeffX χX = 1 := by
    dsimp [coeffX]
    field_simp [hχX_cfNorm_ne_zero, hχX_self]
  have hcoeffXbar_self :
      coeffXbar χXbar = 1 := by
    dsimp [coeffXbar]
    field_simp [hχXbar_cfNorm_ne_zero, hχXbar_self]
  have hcoeffX_Xbar :
      coeffX χXbar = 0 := by
    dsimp [coeffX]
    simp [hχXbar_zero_L]
  have hcoeffXbar_X :
      coeffXbar χX = 0 := by
    dsimp [coeffXbar]
    simp [hχX_zero_Xbar]
  have hTnew_X : Tnew χX = Xbig := by
    dsimp [Tnew]
    simp [hcoeffX_self, hcoeffXbar_X]
  have hTnew_Xbar : Tnew χXbar = Xbarimg := by
    dsimp [Tnew]
    simp [hcoeffX_Xbar, hcoeffXbar_self]
  have hTnew_ψ : Tnew ψ = Told ψ := by
    have hψ_span : integerSpan S1 ψ := hψ_span_S1
    rcases hψ_span with ⟨vψ, hvψ⟩
    rw [hvψ, map_evalCoeff_pf56, map_evalCoeff_pf56]
    refine congrArg (fun μ => Section1.evalCoeff μ vψ) ?_
    funext Y0
    exact hTnew_old Y0
  have hTnew_diffψ : Tnew diffψ = T diffψ := by
    calc
      Tnew diffψ = Tnew χX - Tnew ψ := by
        dsimp [diffψ]
        simp
      _ = Xbig - Told ψ := by rw [hTnew_X, hTnew_ψ]
      _ = Xbig - Y := by rw [hY_eq_Toldψ]
      _ = T diffψ := by simp [hTdiffψ_eq]
  have hTnew_diffX : Tnew diffX = T diffX := by
    calc
      Tnew diffX = Tnew χX - Tnew χXbar := by
        simp [diffX, χXbar]
      _ = Xbig - Xbarimg := by rw [hTnew_X, hTnew_Xbar]
      _ = T diffX := by
            dsimp [Xbarimg]
            abel
  have hpair_ne : χX ≠ χXbar := (h52a X).2
  have hpair_disjoint : Disjoint S1 pair := by
    rw [Finset.disjoint_left]
    intro φ hφS1 hφpair
    simp [pair] at hφpair
    rcases hφpair with hφ | hφ
    · exact hXnotinS1 (hφ ▸ hφS1)
    · exact hXbarNotin (hφ ▸ hφS1)
  let μE : E → Section1.ClassFunction G := fun r => (r : Section1.ClassFunction G)
  let oneE : Section1.CoeffVector E := fun _ => 1
  let μEcomp : Ecomp → Section1.ClassFunction G := fun r => (r : Section1.ClassFunction G)
  let oneEcomp : Section1.CoeffVector Ecomp := fun _ => 1
  have hμEorth :
      ∀ r s : E, Section1.scalarProduct G (μE r) (μE s) = if r = s then 1 else 0 := by
    intro r s
    by_cases hrs : r = s
    · subst hrs
      dsimp [μE]
      simpa using scalarProduct_self_of_signedIrreducible_pf56 (hRX.1 _ (hEsub r.2))
    · dsimp [μE]
      have hrs' : (r : Section1.ClassFunction G) ≠ (s : Section1.ClassFunction G) := by
        intro hEq
        exact hrs (Subtype.ext hEq)
      simpa [hrs] using hRX.2 (hEsub r.2) (hEsub s.2) hrs'
  have hXbig_eval :
      Section1.evalCoeff μE oneE = Finset.sum E (fun φ => φ) := by
    ext g
    simp [Section1.evalCoeff, μE, oneE, ← E.sum_attach]
  have hEcomp_eval :
      Section1.evalCoeff μEcomp oneEcomp = Finset.sum Ecomp (fun φ => φ) := by
    ext g
    simp [Section1.evalCoeff, μEcomp, oneEcomp, ← Ecomp.sum_attach]
  have hXbarimg_eq_negEval :
      Xbarimg = (-1 : ℂ) • Section1.evalCoeff μEcomp oneEcomp := by
    rw [hXbarimg_eq_neg_sum, ← hEcomp_eval]
    simp
  have hXbig_self_raw :
      Section1.scalarProduct G Xbig Xbig = (Section1.coeffDot oneE oneE : ℂ) := by
    rw [hXbig_subset, ← hXbig_eval]
    simpa using
      scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf56 μE hμEorth oneE oneE
  have hXbig_self_cf :
      Section1.scalarProduct G Xbig Xbig = (cfNormSq Xbig : ℂ) := by
    unfold cfNormSq
    rw [hXbig_self_raw]
    simp
  have hXbig_self :
      Section1.scalarProduct G Xbig Xbig = Section1.scalarProduct L χX χX := by
    calc
      Section1.scalarProduct G Xbig Xbig = (cfNormSq Xbig : ℂ) := hXbig_self_cf
      _ = (cfNormSq χX : ℂ) := by rw [hXbig_norm_eq]
      _ = Section1.scalarProduct L χX χX := by symm; exact hχX_self
  have hE_Ecomp_orth : orthogonalFinsets E Ecomp := by
    intro φ ψ hφ hψ
    have hφRX : φ ∈ R X := hEsub hφ
    have hψRX : ψ ∈ R X := hEcomp_subset hψ
    have hne : φ ≠ ψ := by
      intro hEq
      have hψnot : ψ ∉ E := (Finset.mem_sdiff.mp hψ).2
      exact hψnot (hEq.symm ▸ hφ)
    exact hRX.2 hφRX hψRX hne
  have hXbig_orth_Ecomp : orthogonalToFinset Ecomp Xbig := by
    have hsubsetXbig' : isSubsetSumOf E Xbig := ⟨E, subset_rfl, hXbig_subset⟩
    exact orthogonalToFinset_of_subsetSum_of_orthogonalFinsets_pf56
      hsubsetXbig' hE_Ecomp_orth
  have hXbig_Xbar_zero :
      Section1.scalarProduct G Xbig Xbarimg = 0 := by
    rw [hXbarimg_eq_negEval, Section1.scalarProduct_smul_right]
    simp [orthogonalToFinset_scalarProduct_evalCoeff_zero_pf56
      μEcomp (fun r => hXbig_orth_Ecomp r.2) oneEcomp]
  have hXbar_Xbig_zero :
      Section1.scalarProduct G Xbarimg Xbig = 0 := by
    exact scalarProduct_zero_swap_pf56 hXbig_Xbar_zero
  have hTold_old_Xbig_zero :
      ∀ Y0 : S1,
        Section1.scalarProduct G (Told (Y0 : Section1.ClassFunction L)) Xbig = 0 := by
    intro Y0
    rw [hXbig_subset, ← hXbig_eval]
    exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf56 μE
      (fun r => hTold_orth_RX Y0 (hEsub r.2)) oneE
  have hTold_old_Xbar_zero :
      ∀ Y0 : S1,
        Section1.scalarProduct G (Told (Y0 : Section1.ClassFunction L)) Xbarimg = 0 := by
    intro Y0
    rw [hXbarimg_eq_negEval, Section1.scalarProduct_smul_right]
    simp [orthogonalToFinset_scalarProduct_evalCoeff_zero_pf56
      μEcomp (fun r => hTold_orth_RX Y0 (hEcomp_subset r.2)) oneEcomp]
  have hXbig_old_zero :
      ∀ Y0 : S1,
        Section1.scalarProduct G Xbig (Told (Y0 : Section1.ClassFunction L)) = 0 := by
    intro Y0
    exact scalarProduct_zero_swap_pf56 (hTold_old_Xbig_zero Y0)
  have hXbar_old_zero :
      ∀ Y0 : S1,
        Section1.scalarProduct G Xbarimg (Told (Y0 : Section1.ClassFunction L)) = 0 := by
    intro Y0
    exact scalarProduct_zero_swap_pf56 (hTold_old_Xbar_zero Y0)
  have hTdiffX_self :
      Section1.scalarProduct G (T diffX) (T diffX) =
        Section1.scalarProduct L diffX diffX := by
    exact h52b.1 diffX diffX hdiffX_memOn hdiffX_memOn
  have hsource_diffX_self :
      Section1.scalarProduct L diffX diffX =
        Section1.scalarProduct L χX χX + Section1.scalarProduct L χXbar χXbar := by
    dsimp [diffX]
    rw [scalarProduct_sub_left_pf56, scalarProduct_sub_right_pf56,
      scalarProduct_sub_right_pf56]
    rw [hχX_zero_Xbar, hχXbar_zero_L]
    ring
  have htarget_diffX_self :
      Section1.scalarProduct G (T diffX) (T diffX) =
        Section1.scalarProduct G Xbig Xbig + Section1.scalarProduct G Xbarimg Xbarimg := by
    have hTnew_diffX' : Tnew diffX = Xbig - Xbarimg := by
      calc
        Tnew diffX = Tnew χX - Tnew χXbar := by
          simp [diffX, χXbar]
        _ = Xbig - Xbarimg := by rw [hTnew_X, hTnew_Xbar]
    have hTdiffX_eq : T diffX = Xbig - Xbarimg := by
      rw [← hTnew_diffX, hTnew_diffX']
    have hXbig_sub :
        Section1.scalarProduct G Xbig (Xbig - Xbarimg) =
          Section1.scalarProduct G Xbig Xbig := by
      rw [scalarProduct_sub_right_pf56, hXbig_Xbar_zero, sub_zero]
    have hXbar_sub :
        Section1.scalarProduct G Xbarimg (Xbig - Xbarimg) =
          -Section1.scalarProduct G Xbarimg Xbarimg := by
      rw [scalarProduct_sub_right_pf56, hXbar_Xbig_zero]
      ring
    calc
      Section1.scalarProduct G (T diffX) (T diffX) =
          Section1.scalarProduct G (Xbig - Xbarimg) (Xbig - Xbarimg) := by
            rw [hTdiffX_eq]
      _ = Section1.scalarProduct G Xbig (Xbig - Xbarimg) -
            Section1.scalarProduct G Xbarimg (Xbig - Xbarimg) := by
            rw [scalarProduct_sub_left_pf56]
      _ = Section1.scalarProduct G Xbig Xbig + Section1.scalarProduct G Xbarimg Xbarimg := by
            rw [hXbig_sub, hXbar_sub]
            ring
  have hXbarimg_self :
      Section1.scalarProduct G Xbarimg Xbarimg = Section1.scalarProduct L χXbar χXbar := by
    calc
      Section1.scalarProduct G Xbarimg Xbarimg =
          (Section1.scalarProduct G Xbig Xbig +
            Section1.scalarProduct G Xbarimg Xbarimg) -
            Section1.scalarProduct G Xbig Xbig := by ring
      _ = Section1.scalarProduct G (T diffX) (T diffX) -
            Section1.scalarProduct G Xbig Xbig := by rw [htarget_diffX_self]
      _ = Section1.scalarProduct L diffX diffX -
            Section1.scalarProduct G Xbig Xbig := by rw [hTdiffX_self]
      _ = Section1.scalarProduct L χXbar χXbar := by
            rw [hsource_diffX_self, hXbig_self]
            ring
  have hXbig_virt : Theory.Character.IsVirtualCharacter Xbig := by
    rw [hXbig_subset]
    refine isVirtualCharacter_finset_sum_pf56 E (fun φ => φ) ?_
    intro φ hφ
    exact isVirtualCharacter_of_signedIrreducible_pf56 (hRX.1 _ (hEsub hφ))
  have hXbarimg_virt : Theory.Character.IsVirtualCharacter Xbarimg := by
    have hsum_virt :
        Theory.Character.IsVirtualCharacter (Finset.sum Ecomp (fun φ => φ)) := by
      refine isVirtualCharacter_finset_sum_pf56 Ecomp (fun φ => φ) ?_
      intro φ hφ
      exact isVirtualCharacter_of_signedIrreducible_pf56 (hRX.1 _ (hEcomp_subset hφ))
    simpa [hXbarimg_eq_neg_sum] using Section3.isVirtualCharacter_neg hsum_virt
  let μSnew : Snew → Section1.ClassFunction L := fun Y => (Y : Section1.ClassFunction L)
  let νSnew : Snew → Section1.ClassFunction G := fun Y => Tnew (Y : Section1.ClassFunction L)
  have hgramSnew :
      ∀ i j : Snew,
        Section1.scalarProduct G (νSnew i) (νSnew j) =
          Section1.scalarProduct L (μSnew i) (μSnew j) := by
    intro i j
    by_cases hiOld : (i : Section1.ClassFunction L) ∈ S1
    · by_cases hjOld : (j : Section1.ClassFunction L) ∈ S1
      · let iOld : S1 := ⟨(i : Section1.ClassFunction L), hiOld⟩
        let jOld : S1 := ⟨(j : Section1.ClassFunction L), hjOld⟩
        calc
          Section1.scalarProduct G (νSnew i) (νSnew j) =
              Section1.scalarProduct G
                (Tnew (iOld : Section1.ClassFunction L))
                (Tnew (jOld : Section1.ClassFunction L)) := by
                  simp [νSnew, iOld, jOld]
          _ =
              Section1.scalarProduct G
                (Told (iOld : Section1.ClassFunction L))
                (Told (jOld : Section1.ClassFunction L)) := by
                  rw [hTnew_old iOld, hTnew_old jOld]
          _ = Section1.scalarProduct L
                (iOld : Section1.ClassFunction L)
                (jOld : Section1.ClassFunction L) := by
                  exact hIsoOld _ _
                    (integerSpan_of_mem_pf56 S1 iOld.2)
                    (integerSpan_of_mem_pf56 S1 jOld.2)
          _ = Section1.scalarProduct L (μSnew i) (μSnew j) := by
                simp [μSnew, iOld, jOld]
      · have hjpair : (j : Section1.ClassFunction L) ∈ pair := by
          have hjSnew : (j : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact j.2
          exact (Finset.mem_union.mp hjSnew).resolve_left hjOld
        have hjpair_eq : (j : Section1.ClassFunction L) = χX ∨
            (j : Section1.ClassFunction L) = χXbar := by
          simpa [pair] using hjpair
        rcases hjpair_eq with hjX | hjXbar
        · have hsrc :
              Section1.scalarProduct L (i : Section1.ClassFunction L) χX = 0 := by
            exact h52c (χ := (i : Section1.ClassFunction L)) (ψ := χX)
              (hS1subset hiOld) X.2 (by
                intro hEq
                exact hXnotinS1 (hEq.symm ▸ hiOld))
          have hzero := hTold_old_Xbig_zero ⟨(i : Section1.ClassFunction L), hiOld⟩
          rw [← hTnew_old ⟨(i : Section1.ClassFunction L), hiOld⟩] at hzero
          simpa [νSnew, μSnew, hTnew_X, hsrc, hjX] using hzero
        · have hsrc :
              Section1.scalarProduct L
                  (i : Section1.ClassFunction L) χXbar = 0 := by
            exact h52c (χ := (i : Section1.ClassFunction L)) (ψ := χXbar)
              (hS1subset hiOld) ((h52a X).1) (by
                intro hEq
                have hmem : χXbar ∈ S1 := hEq.symm ▸ hiOld
                exact hXbarNotin (by simpa [χXbar] using hmem))
          have hzero := hTold_old_Xbar_zero ⟨(i : Section1.ClassFunction L), hiOld⟩
          rw [← hTnew_old ⟨(i : Section1.ClassFunction L), hiOld⟩] at hzero
          simpa [νSnew, μSnew, hTnew_Xbar, hsrc, hjXbar] using hzero
    · by_cases hjOld : (j : Section1.ClassFunction L) ∈ S1
      · have hipair : (i : Section1.ClassFunction L) ∈ pair := by
          have hiSnew : (i : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact i.2
          exact (Finset.mem_union.mp hiSnew).resolve_left hiOld
        have hipair_eq : (i : Section1.ClassFunction L) = χX ∨
            (i : Section1.ClassFunction L) = χXbar := by
          simpa [pair] using hipair
        rcases hipair_eq with hiX | hiXbar
        · have hsrc :
              Section1.scalarProduct L χX (j : Section1.ClassFunction L) = 0 := by
            exact scalarProduct_zero_swap_pf56 <|
              h52c (χ := (j : Section1.ClassFunction L)) (ψ := χX)
                (hS1subset hjOld) X.2 (by
                  intro hEq
                  exact hXnotinS1 (hEq.symm ▸ hjOld))
          have hzero := hXbig_old_zero ⟨(j : Section1.ClassFunction L), hjOld⟩
          rw [← hTnew_old ⟨(j : Section1.ClassFunction L), hjOld⟩] at hzero
          simpa [νSnew, μSnew, hTnew_X, hsrc, hiX] using hzero
        · have hsrc :
              Section1.scalarProduct L χXbar (j : Section1.ClassFunction L) = 0 := by
            exact scalarProduct_zero_swap_pf56 <|
              h52c (χ := (j : Section1.ClassFunction L)) (ψ := χXbar)
                (hS1subset hjOld) ((h52a X).1) (by
                  intro hEq
                  have hmem : χXbar ∈ S1 := hEq.symm ▸ hjOld
                  exact hXbarNotin (by simpa [χXbar] using hmem))
          have hzero := hXbar_old_zero ⟨(j : Section1.ClassFunction L), hjOld⟩
          rw [← hTnew_old ⟨(j : Section1.ClassFunction L), hjOld⟩] at hzero
          simpa [νSnew, μSnew, hTnew_Xbar, hsrc, hiXbar] using hzero
      · have hipair : (i : Section1.ClassFunction L) = χX ∨
            (i : Section1.ClassFunction L) = χXbar := by
          have hiSnew : (i : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact i.2
          have hipair' : (i : Section1.ClassFunction L) ∈ pair :=
            (Finset.mem_union.mp hiSnew).resolve_left hiOld
          simpa [pair] using hipair'
        have hjpair : (j : Section1.ClassFunction L) = χX ∨
            (j : Section1.ClassFunction L) = χXbar := by
          have hjSnew : (j : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact j.2
          have hjpair' : (j : Section1.ClassFunction L) ∈ pair :=
            (Finset.mem_union.mp hjSnew).resolve_left hjOld
          simpa [pair] using hjpair'
        rcases hipair with hiX | hiXbar <;> rcases hjpair with hjX | hjXbar
        · simpa [νSnew, μSnew, hTnew_X, hiX, hjX] using hXbig_self
        · simpa [νSnew, μSnew, hTnew_X, hTnew_Xbar, hiX, hjXbar, hχX_zero_Xbar] using
            hXbig_Xbar_zero
        · simpa [νSnew, μSnew, hTnew_X, hTnew_Xbar, hiXbar, hjX, hχXbar_zero_L] using
            hXbar_Xbig_zero
        · simpa [νSnew, μSnew, hTnew_Xbar, hiXbar, hjXbar] using hXbarimg_self
  have hIsoNew :
      isCFLinearIsometryOnSpan Snew Tnew := by
    intro φ ψ' hφ hψ'
    rcases hφ with ⟨v, hv⟩
    rcases hψ' with ⟨w, hw⟩
    rw [hv, hw, map_evalCoeff_pf56, map_evalCoeff_pf56]
    simpa [μSnew, νSnew] using
      scalarProduct_evalCoeff_eq_of_gram_eq_pf56 μSnew νSnew hgramSnew v w
  have hVirtNew :
      mapsIntegerSpanToVirtualCharacters Snew Tnew := by
    intro χ hχ
    rcases hχ with ⟨v, hv⟩
    let μT : Snew → Section1.ClassFunction G := fun Y => Tnew (Y : Section1.ClassFunction L)
    have hμTvirt : ∀ Y : Snew, Theory.Character.IsVirtualCharacter (μT Y) := by
      intro Y
      by_cases hYold : (Y : Section1.ClassFunction L) ∈ S1
      · let Y0 : S1 := ⟨(Y : Section1.ClassFunction L), hYold⟩
        have hYspan : integerSpan S1 (Y0 : Section1.ClassFunction L) :=
          integerSpan_of_mem_pf56 S1 Y0.2
        have hvirt := hVirtOld (Y0 : Section1.ClassFunction L) hYspan
        rw [← hTnew_old Y0] at hvirt
        simpa [μT, Y0] using hvirt
      · have hYpair : (Y : Section1.ClassFunction L) = χX ∨
            (Y : Section1.ClassFunction L) = χXbar := by
          have hYSnew : (Y : Section1.ClassFunction L) ∈ S1 ∪ pair := by
            exact Y.2
          have hYpair' : (Y : Section1.ClassFunction L) ∈ pair := by
            exact (Finset.mem_union.mp hYSnew).resolve_left hYold
          simpa [pair] using hYpair'
        rcases hYpair with hYX | hYXbar
        · simpa [μT, hTnew_X, hYX] using hXbig_virt
        · simpa [μT, hTnew_Xbar, hYXbar] using hXbarimg_virt
    rw [hv, map_evalCoeff_pf56]
    exact isVirtualCharacter_evalCoeff_pf56 μT hμTvirt v
  have hAgreeNew :
      agreesOnIntegerSpanOn Snew puncturedSet T Tnew := by
    intro χ hχ
    rcases hχ with ⟨hχspan, hχon⟩
    rcases hχspan with ⟨v, hv⟩
    let vOld : Section1.CoeffVector S1 := fun Y0 =>
      v ⟨(Y0 : Section1.ClassFunction L), hOld_le_Snew Y0.2⟩
    let m : Int := v ⟨χX, hX_mem_Snew⟩
    let n : Int := v ⟨χXbar, hXbar_mem_Snew⟩
    let s : Int := m + n
    let oldSum : Section1.ClassFunction L :=
      Section1.evalCoeff (fun Y0 : S1 => (Y0 : Section1.ClassFunction L)) vOld
    let oldPart : Section1.ClassFunction L := oldSum + (s : ℂ) • ψ
    have hχ_split :
        χ = oldSum + (m : ℂ) • χX + (n : ℂ) • χXbar := by
      rw [hv]
      ext g
      let coeff : Section1.ClassFunction L → ℂ := fun φ =>
        if hφ : φ ∈ Snew then (v ⟨φ, hφ⟩ : ℂ) else 0
      have hsplit :
          Finset.sum Snew (fun φ => coeff φ * φ g) =
            Finset.sum S1 (fun φ => coeff φ * φ g) +
              Finset.sum pair (fun φ => coeff φ * φ g) := by
        rw [show Snew = S1 ∪ pair by rfl, Finset.sum_union hpair_disjoint]
      have hleft :
          (∑ x : Snew, (v x : ℂ) • (x : Section1.ClassFunction L)) g =
            Finset.sum Snew (fun φ => coeff φ * φ g) := by
        rw [Finset.sum_apply, Finset.univ_eq_attach]
        calc
          ∑ x ∈ Snew.attach, ((v x : ℂ) • x.1) g
              = ∑ x ∈ Snew.attach, coeff x.1 * x.1 g := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  have hcoeffx : coeff x.1 = (v x : ℂ) := by
                    simp [coeff, x.2]
                  calc
                    ((v x : ℂ) • x.1) g = (v x : ℂ) * x.1 g := by
                      simp [smul_eq_mul]
                    _ = coeff x.1 * x.1 g := by
                      rw [← hcoeffx]
          _ = Finset.sum Snew (fun φ => coeff φ * φ g) := by
                exact Snew.sum_attach (f := fun φ => coeff φ * φ g)
      have hold :
          oldSum g = Finset.sum S1 (fun φ => coeff φ * φ g) := by
        rw [show oldSum = Section1.evalCoeff (fun Y0 : S1 => (Y0 : Section1.ClassFunction L)) vOld by
          rfl]
        rw [Section1.evalCoeff, Finset.sum_apply, Finset.univ_eq_attach]
        calc
          ∑ x ∈ S1.attach, ((vOld x : ℂ) • x.1) g
              = ∑ x ∈ S1.attach, coeff x.1 * x.1 g := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  have hxSnew : (x : Section1.ClassFunction L) ∈ Snew := hOld_le_Snew x.2
                  have hcoeffx : coeff x.1 = (vOld x : ℂ) := by
                    simp [vOld, coeff, hxSnew]
                  calc
                    ((vOld x : ℂ) • x.1) g = (vOld x : ℂ) * x.1 g := by
                      simp [smul_eq_mul]
                    _ = coeff x.1 * x.1 g := by
                      rw [← hcoeffx]
          _ = Finset.sum S1 (fun φ => coeff φ * φ g) := by
                exact S1.sum_attach (f := fun φ => coeff φ * φ g)
      have hpairsum :
          Finset.sum pair (fun φ => coeff φ * φ g) =
            ↑(v ⟨χX, hX_mem_Snew⟩) * χX g + ↑(v ⟨χXbar, hXbar_mem_Snew⟩) * χXbar g := by
        rw [show pair = insert χX ({χXbar} : Finset (Section1.ClassFunction L)) by
          simp [pair, χXbar]]
        rw [Finset.sum_insert, Finset.sum_singleton]
        · simp [coeff, hX_mem_Snew, hXbar_mem_Snew, χXbar]
        · simpa [Finset.mem_singleton, χXbar] using hpair_ne
      calc
        (∑ x : Snew, (v x : ℂ) • (x : Section1.ClassFunction L)) g =
            Finset.sum Snew (fun φ => coeff φ * φ g) := hleft
        _ = Finset.sum S1 (fun φ => coeff φ * φ g) +
            Finset.sum pair (fun φ => coeff φ * φ g) := hsplit
        _ = oldSum g +
            (↑(v ⟨χX, hX_mem_Snew⟩) * χX g + ↑(v ⟨χXbar, hXbar_mem_Snew⟩) * χXbar g) := by
              rw [← hold, hpairsum]
        _ = (oldSum + (m : ℂ) • χX + (n : ℂ) • χXbar) g := by
              dsimp [m, n, χXbar]
              simp [add_assoc]
    have hχ_decomp :
        χ = oldPart + (s : ℂ) • diffψ - (n : ℂ) • diffX := by
      calc
        χ = oldSum + (m : ℂ) • χX + (n : ℂ) • χXbar := hχ_split
        _ = oldPart + (s : ℂ) • diffψ - (n : ℂ) • diffX := by
              ext g
              dsimp [χXbar]
              dsimp [oldPart, oldSum, s, m, n, diffψ, diffX, ψ]
              simp [sub_eq_add_neg]
              ring_nf
    have hOldSum_span : integerSpan S1 oldSum := by
      refine ⟨vOld, rfl⟩
    have hOldPart_span : integerSpan S1 oldPart := by
      exact integerSpan_add_pf56 hOldSum_span (integerSpan_zsmul_pf56 s hψ_span_S1)
    have hOldPart_eq :
        oldPart = χ + (-(s : ℂ)) • diffψ + (n : ℂ) • diffX := by
      calc
        oldPart = (oldPart + (s : ℂ) • diffψ - (n : ℂ) • diffX) +
            (-(s : ℂ)) • diffψ + (n : ℂ) • diffX := by
              ext g
              dsimp [oldPart, diffψ, diffX, ψ]
              ring_nf
        _ = χ + (-(s : ℂ)) • diffψ + (n : ℂ) • diffX := by
              rw [hχ_decomp]
    have hOldPart_on : Section1.supportedOn oldPart puncturedSet := by
      rw [hOldPart_eq]
      exact supportedOn_add_pf56
        (supportedOn_add_pf56 hχon (supportedOn_smul_pf56 (-(s : ℂ)) hdiffψ_on))
        (supportedOn_smul_pf56 (n : ℂ) hdiffX_on)
    have hOldPart_memOn : integerSpanOn S1 puncturedSet oldPart :=
      ⟨hOldPart_span, hOldPart_on⟩
    have hTnew_oldSum : Tnew oldSum = Told oldSum := by
      dsimp [oldSum, vOld]
      rw [map_evalCoeff_pf56, map_evalCoeff_pf56]
      simp [Section1.evalCoeff, hTnew_old]
    have hTnew_oldPart : Tnew oldPart = Told oldPart := by
      dsimp [oldPart]
      simp [map_add, map_smul, hTnew_oldSum, hTnew_ψ]
    calc
      Tnew χ = Tnew (oldPart + (s : ℂ) • diffψ - (n : ℂ) • diffX) := by rw [hχ_decomp]
      _ = Tnew oldPart + (s : ℂ) • Tnew diffψ - (n : ℂ) • Tnew diffX := by
            rw [map_sub, map_add, map_smul, map_smul]
      _ = Told oldPart + (s : ℂ) • T diffψ - (n : ℂ) • T diffX := by
            rw [hTnew_oldPart, hTnew_diffψ, hTnew_diffX]
      _ = T oldPart + (s : ℂ) • T diffψ - (n : ℂ) • T diffX := by
            rw [hAgreeOld oldPart hOldPart_memOn]
      _ = T (oldPart + (s : ℂ) • diffψ - (n : ℂ) • diffX) := by
            ext g
            dsimp [oldPart, diffψ, ψ]
            simp [map_add, map_sub, map_smul]
      _ = T χ := by rw [hχ_decomp]
  have hdiffX_span_Snew : integerSpan Snew diffX := by
    exact integerSpan_sub_pf56
      (integerSpan_of_mem_pf56 Snew hX_mem_Snew)
      (integerSpan_of_mem_pf56 Snew hXbar_mem_Snew)
  have hdiffX_ne_zero : diffX ≠ 0 := by
    intro hzero
    exact (h52a X).2 (by
      simpa [diffX, χXbar] using sub_eq_zero.mp hzero)
  have hSnew_nonempty : integerSpanOnNonempty Snew puncturedSet :=
    ⟨diffX, ⟨hdiffX_span_Snew, hdiffX_on⟩, hdiffX_ne_zero⟩
  have hSnew_virtual : sourceVirtualCharacters Snew := by
    intro χ hχ
    rw [Finset.mem_union] at hχ
    rcases hχ with hχS1 | hχpair
    · exact isVirtualCharacter_of_isCharacter
        (hsetup.2 ⟨χ, hS1subset hχS1⟩)
    · rw [Finset.mem_insert, Finset.mem_singleton] at hχpair
      rcases hχpair with hχX | hχXbar
      · subst χ
        exact isVirtualCharacter_of_isCharacter (hsetup.2 X)
      · subst χ
        exact isVirtualCharacter_of_isCharacter
          (hsetup.2 ⟨χXbar, (h52a X).1⟩)
  exact ⟨hSnew_virtual, hSnew_nonempty, Tnew, hIsoNew, hVirtNew, hAgreeNew⟩

end CFSG.Section5

module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 5, Theorem (5.7)

This file isolates PF `(5.7)` as its own proof target.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section5

universe v
universe u

/-! ## (5.7) -/

/--
Peterfalvi `(5.7)`: if Hypothesis `(5.2)` holds and every member of `S` has
the same degree, then `S` is coherent.
-/
@[expose] public def theorem_5_7_statement
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
                (∀ X Y : S,
                  Section1.degree (X : Section1.ClassFunction L) =
                    Section1.degree (Y : Section1.ClassFunction L)) →
                  definition_5_1_statement puncturedSet S T


private theorem integerSpan_of_mem_pf57
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

private theorem integerSpan_mono_pf57
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
        intro y _hyS2 hyS1
        simp [hyS1])
  simpa +contextual [Section1.evalCoeff, w, smul_eq_mul, ← S1.sum_attach,
    ← S2.sum_attach] using hsum

private theorem integerSpan_add_pf57
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ + ψ) := by
  classical
  rintro ⟨v, rfl⟩ ⟨w, rfl⟩
  refine ⟨v + w, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.sum_add_distrib, add_mul]

private theorem integerSpan_neg_pf57
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H} :
    integerSpan S φ → integerSpan S (-φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  ext g
  simp [Section1.evalCoeff]

private theorem integerSpan_sub_pf57
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ - ψ) := by
  intro hφ hψ
  simpa [sub_eq_add_neg] using integerSpan_add_pf57 hφ (integerSpan_neg_pf57 hψ)

private theorem integerSpan_zsmul_pf57
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H} (z : Int) :
    integerSpan S φ → integerSpan S ((z : ℂ) • φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨z • v, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.mul_sum, mul_assoc]

private theorem supportedOn_zero_pf57
    {H : Type*} [Group H]
    {A : Set H} :
    Section1.supportedOn (0 : Section1.ClassFunction H) A := by
  rw [Section1.supportedOn_iff]
  intro g hg
  simp

private theorem supportedOn_add_pf57
    {H : Type*} [Group H]
    {A : Set H}
    {φ ψ : Section1.ClassFunction H}
    (hφ : Section1.supportedOn φ A)
    (hψ : Section1.supportedOn ψ A) :
    Section1.supportedOn (φ + ψ) A := by
  rw [Section1.supportedOn_iff] at hφ hψ ⊢
  intro g hg
  simp [hφ g hg, hψ g hg]

private theorem supportedOn_smul_pf57
    {H : Type*} [Group H]
    {A : Set H}
    {φ : Section1.ClassFunction H}
    (z : ℂ)
    (hφ : Section1.supportedOn φ A) :
    Section1.supportedOn (z • φ) A := by
  rw [Section1.supportedOn_iff] at hφ ⊢
  intro g hg
  simp [hφ g hg]

private theorem integerSpanOn_add_pf57
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {A : Set H}
    {φ ψ : Section1.ClassFunction H} :
    integerSpanOn S A φ → integerSpanOn S A ψ → integerSpanOn S A (φ + ψ) := by
  rintro ⟨hφ_span, hφ_on⟩ ⟨hψ_span, hψ_on⟩
  exact ⟨integerSpan_add_pf57 hφ_span hψ_span, supportedOn_add_pf57 hφ_on hψ_on⟩


private theorem integerSpanOn_zsmul_pf57
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {A : Set H}
    {φ : Section1.ClassFunction H} (z : Int) :
    integerSpanOn S A φ → integerSpanOn S A ((z : ℂ) • φ) := by
  rintro ⟨hφ_span, hφ_on⟩
  exact ⟨integerSpan_zsmul_pf57 z hφ_span, supportedOn_smul_pf57 (z : ℂ) hφ_on⟩

private theorem integerSpanOn_sum_pf57
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
    exact integerSpanOn_zsmul_pf57 (v i) (hμ i)
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa [f] using
        (show integerSpanOn S A (0 : Section1.ClassFunction H) from
          ⟨⟨0, by simp [Section1.evalCoeff]⟩, supportedOn_zero_pf57⟩)
  | @insert i t hit ih =>
      have ht : integerSpanOn S A (Finset.sum t f) := by
        simpa [f] using ih
      have hi : integerSpanOn S A (f i) := hf i
      simpa [f, Finset.sum_insert hit] using integerSpanOn_add_pf57 hi ht

private theorem integerSpanOn_of_generators_pf57
    {H : Type*} [Group H]
    {S U : Finset (Section1.ClassFunction H)}
    {A : Set H}
    {φ : Section1.ClassFunction H}
    (hU : ∀ ψ : Section1.ClassFunction H, ψ ∈ U → integerSpanOn S A ψ) :
    integerSpan U φ → integerSpanOn S A φ := by
  classical
  rintro ⟨v, rfl⟩
  exact integerSpanOn_sum_pf57
    (μ := fun ψ : U => (ψ : Section1.ClassFunction H))
    (hμ := fun ψ => hU ψ ψ.2)
    v

private theorem scalarProduct_zero_swap_pf57
    {H : Type*} [Finite H]
    {φ ψ : Section1.ClassFunction H}
    (h : Section1.scalarProduct H φ ψ = 0) :
    Section1.scalarProduct H ψ φ = 0 := by
  simpa [Section1.scalarProduct_star_swap] using congrArg star h

private theorem scalarProduct_add_right_pf57
    {H : Type*} [Finite H]
    (φ ψ1 ψ2 : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ1 + ψ2) =
      Section1.scalarProduct H φ ψ1 + Section1.scalarProduct H φ ψ2 := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_sub_right_pf57
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
            rw [scalarProduct_add_right_pf57]
    _ = Section1.scalarProduct H φ ψ1 - Section1.scalarProduct H φ ψ2 := by
          rw [Section1.scalarProduct_smul_right]
          simp [sub_eq_add_neg]

private theorem scalarProduct_sub_left_pf57
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

private theorem scalarProduct_conjugate_left_pf57
    {G : Type*} [Finite G] (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Section1.conjugateCharacter φ) ψ =
      star (Section1.scalarProduct G φ (Section1.conjugateCharacter ψ)) := by
  simp [Section1.scalarProduct, Section1.conjugateCharacter]

private theorem conjugateCharacter_involutive_pf57
    {G : Type*} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    Section1.conjugateCharacter (Section1.conjugateCharacter φ) = φ := by
  ext g
  simp [Section1.conjugateCharacter]

private theorem scalarProduct_self_of_irreducibleCharacterOnGroup_pf57
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  simpa using Section1.scalarProduct_representation_char_self ρ hρ

private theorem scalarProduct_self_of_signedIrreducible_pf57
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμself : Section1.scalarProduct G μ μ = 1 :=
    scalarProduct_self_of_irreducibleCharacterOnGroup_pf57 hμ
  rcases hε with rfl | rfl
  · simp [hμself]
  · calc
      Section1.scalarProduct G ((-1 : ℂ) • μ) ((-1 : ℂ) • μ)
          = (-1 : ℂ) * (star (-1 : ℂ)) * Section1.scalarProduct G μ μ := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
              ring
      _ = 1 := by simp [hμself]

private theorem scalarProduct_eq_ite_of_signedOrthonormalFinset_pf57
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R) :
    ∀ a b : R, Section1.scalarProduct G (a : Section1.ClassFunction G) b =
      if a = b then 1 else 0 := by
  intro a b
  by_cases hab : a = b
  · subst hab
    simpa using scalarProduct_self_of_signedIrreducible_pf57 (hR.1 _ a.2)
  · simpa [hab] using hR.2 a.2 b.2 (fun hEq => hab (Subtype.ext hEq))

private theorem scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf57
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

private theorem supportedOn_puncturedSet_iff_degree_eq_zero_pf57
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

private theorem cfNormSq_eq_inv_card_mul_sum_normSq_pf57
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

private theorem cfNormSq_nonneg_pf57
    {H : Type*} [Group H] [Finite H]
    (φ : Section1.ClassFunction H) :
    0 ≤ cfNormSq φ := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf57]
  have hcard : 0 ≤ (Nat.card H : ℝ)⁻¹ := by positivity
  have hsum : 0 ≤ ∑ g : H, Complex.normSq (φ g) := by
    refine Finset.sum_nonneg ?_
    intro g _hg
    exact Complex.normSq_nonneg (φ g)
  exact mul_nonneg hcard hsum

private theorem cfNormSq_eq_zero_pf57
    {H : Type*} [Group H] [Finite H]
    {φ : Section1.ClassFunction H}
    (hφ : cfNormSq φ = 0) :
    φ = 0 := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf57] at hφ
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

private theorem degree_eq_nat_of_isCharacter_pf57
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsCharacter χ) :
    ∃ d : ℕ, Section1.degree χ = (d : ℂ) := by
  rcases hχ with ⟨V, _hadd, _hmod, _hfd, ρ, rfl⟩
  exact ⟨Module.finrank ℂ V, Section1.degree_representation_character ρ⟩

private theorem degree_conjugateCharacter_eq_of_isCharacter_pf57
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsCharacter χ) :
    Section1.degree (Section1.conjugateCharacter χ) = Section1.degree χ := by
  rcases degree_eq_nat_of_isCharacter_pf57 hχ with ⟨d, hd⟩
  calc
    Section1.degree (Section1.conjugateCharacter χ) = star (Section1.degree χ) := by
      simp [Section1.degree, Section1.conjugateCharacter]
    _ = Section1.degree χ := by
      rw [hd]
      simp

private theorem character_eq_zero_of_degree_zero_pf57
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

private theorem isVirtualCharacter_of_signedIrreducible_pf57
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Theory.Character.IsVirtualCharacter χ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hμ
  · simpa using Section3.isVirtualCharacter_neg
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hμ)

private theorem isVirtualCharacter_zsmul_pf57
    {G : Type u} [Group G] [Finite G]
    (n : ℤ) {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (n • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isVirtualCharacter_finset_sum_pf57
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

private theorem isVirtualCharacter_evalCoeff_pf57
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G)
    (hμ : ∀ i, Theory.Character.IsVirtualCharacter (μ i))
    (v : Section1.CoeffVector ι) :
    Theory.Character.IsVirtualCharacter (Section1.evalCoeff μ v) := by
  classical
  rw [Section1.evalCoeff]
  refine isVirtualCharacter_finset_sum_pf57 (Finset.univ : Finset ι)
    (fun i => ((v i : ℂ) • μ i)) ?_
  intro i _hi
  have hsmul :
      (v i : ℂ) • μ i = (v i • μ i : Section1.ClassFunction G) := by
    ext g
    simp [zsmul_eq_mul]
  rw [hsmul]
  exact isVirtualCharacter_zsmul_pf57 (v i) (hμ i)

private theorem scalarProduct_self_eq_cfNormSq_of_character_pf57
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

private theorem orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
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

private theorem orthogonalToFinset_of_subsetSum_of_orthogonalFinsets_pf57
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
  | @insert a E ha ih =>
      rw [Finset.sum_insert ha, Section1.scalarProduct_add_left]
      have ha0 : Section1.scalarProduct H a ψ = 0 := horth (hE (by simp)) hψ
      have hE0 : Section1.scalarProduct H (Finset.sum E fun χ => χ) ψ = 0 := by
        refine ih ?_
        intro χ hχ
        exact hE (by simp [hχ])
      simp [ha0, hE0]

private theorem orthogonalToFinset_add_pf57
    {H : Type*} [Group H] [Finite H]
    {R : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H}
    (hφ : orthogonalToFinset R φ)
    (hψ : orthogonalToFinset R ψ) :
    orthogonalToFinset R (φ + ψ) := by
  intro χ hχ
  rw [Section1.scalarProduct_add_left]
  simp [hφ hχ, hψ hχ]

private theorem orthogonalToFinset_neg_pf57
    {H : Type*} [Group H] [Finite H]
    {R : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H}
    (hφ : orthogonalToFinset R φ) :
    orthogonalToFinset R (-φ) := by
  intro χ hχ
  have hsmul : Section1.scalarProduct H (((-1 : ℂ) • φ)) χ = 0 := by
    rw [Section1.scalarProduct_smul_left]
    simp [hφ hχ]
  simpa using hsmul

private theorem orthogonalToFinset_sub_pf57
    {H : Type*} [Group H] [Finite H]
    {R : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H}
    (hφ : orthogonalToFinset R φ)
    (hψ : orthogonalToFinset R ψ) :
    orthogonalToFinset R (φ - ψ) := by
  simpa [sub_eq_add_neg] using orthogonalToFinset_add_pf57 hφ (orthogonalToFinset_neg_pf57 hψ)

public theorem orthogonalToFinset_of_integerSpan_of_orthogonalFinsets_pf57
    {H : Type*} [Group H] [Finite H]
    {R1 R2 : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H}
    (hspan : integerSpan R1 φ)
    (horth : orthogonalFinsets R1 R2) :
    orthogonalToFinset R2 φ := by
  classical
  rcases hspan with ⟨v, rfl⟩
  intro ψ hψ
  let μ : R1 → Section1.ClassFunction H := fun r => (r : Section1.ClassFunction H)
  have hzero : Section1.scalarProduct H ψ (Section1.evalCoeff μ v) = 0 := by
    apply orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57 μ
    intro r
    exact scalarProduct_zero_swap_pf57 (horth r.2 hψ)
  exact scalarProduct_zero_swap_pf57 hzero

private theorem cfNormSq_sub_eq_add_of_orthogonal_pf57
    {H : Type*} [Group H] [Finite H]
    {φ ψ : Section1.ClassFunction H}
    (hφψ : Section1.scalarProduct H φ ψ = 0)
    (hψφ : Section1.scalarProduct H ψ φ = 0) :
    cfNormSq (φ - ψ) = cfNormSq φ + cfNormSq ψ := by
  unfold cfNormSq
  rw [scalarProduct_sub_left_pf57, scalarProduct_sub_right_pf57, scalarProduct_sub_right_pf57]
  simp [hφψ, hψφ]

private theorem cfNormSq_add_eq_add_of_orthogonal_pf57
    {H : Type*} [Group H] [Finite H]
    {φ ψ : Section1.ClassFunction H}
    (hφψ : Section1.scalarProduct H φ ψ = 0)
    (hψφ : Section1.scalarProduct H ψ φ = 0) :
    cfNormSq (φ + ψ) = cfNormSq φ + cfNormSq ψ := by
  unfold cfNormSq
  rw [Section1.scalarProduct_add_left, scalarProduct_add_right_pf57,
    scalarProduct_add_right_pf57]
  simp [hφψ, hψφ]

private theorem orthogonal_projection_decomposition_pf57
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
    scalarProduct_eq_ite_of_signedOrthonormalFinset_pf57 hR
  let coeffs : Section1.CoeffVector R := fun r =>
    Classical.choose <|
      Section3.scalarProduct_isVirtualCharacter_eq_int
        hηvirt
        (isVirtualCharacter_of_signedIrreducible_pf57 (hR.1 _ r.2))
  have hcoeffs :
      ∀ r : R,
        Section1.scalarProduct G η (μ r) = (coeffs r : ℂ) := by
    intro r
    exact Classical.choose_spec <|
      Section3.scalarProduct_isVirtualCharacter_eq_int
        hηvirt
        (isVirtualCharacter_of_signedIrreducible_pf57 (hR.1 _ r.2))
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
                scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf57
                  μ hμorth coeffs (Section1.basisVector r)
        _ = (coeffs r : ℂ) := by
              simp [Section1.coeffDot, Section1.basisVector]
    dsimp [Y]
    rw [scalarProduct_sub_left_pf57]
    simpa [μ] using sub_eq_zero.mpr (hXbigCoeff.trans (hcoeffs r).symm)
  · dsimp [Y]
    ext g
    simp

private theorem integerSpan_eq_zero_of_orthogonal_pf57
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R)
    {φ : Section1.ClassFunction G}
    (hφspan : integerSpan R φ)
    (hφorth : orthogonalToFinset R φ) :
    φ = 0 := by
  classical
  rcases hφspan with ⟨v, rfl⟩
  let μ : R → Section1.ClassFunction G := fun r => (r : Section1.ClassFunction G)
  have hμorth :
      ∀ a b : R,
        Section1.scalarProduct G (μ a) (μ b) = if a = b then 1 else 0 :=
    scalarProduct_eq_ite_of_signedOrthonormalFinset_pf57 hR
  have hvzero : ∀ r : R, v r = 0 := by
    intro r
    have hμbasis :
        Section1.evalCoeff μ (Section1.basisVector r) = μ r := by
      ext g
      rw [Section1.evalCoeff, Finset.sum_eq_single r]
      · simp [Section1.basisVector]
      · intro s _hs hsr
        simp [Section1.basisVector, hsr]
      · intro hrFalse
        exact (hrFalse (Finset.mem_univ _)).elim
    have hzero :
        Section1.scalarProduct G (Section1.evalCoeff μ v) (μ r) = 0 := hφorth r.2
    rw [← hμbasis] at hzero
    have hcoeff :
        Section1.scalarProduct G (Section1.evalCoeff μ v)
            (Section1.evalCoeff μ (Section1.basisVector r)) =
          (Section1.coeffDot v (Section1.basisVector r) : ℂ) := by
      simpa using
        scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf57
          μ hμorth v (Section1.basisVector r)
    rw [hcoeff, Section1.coeffDot, Finset.sum_eq_single r] at hzero
    · simpa [Section1.basisVector] using hzero
    · intro s _hs hsr
      simp [Section1.basisVector, hsr]
    · intro hrFalse
      exact (hrFalse (Finset.mem_univ _)).elim
  ext g
  simp [Section1.evalCoeff, hvzero]

private theorem projection_component_unique_pf57
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R)
    {A B U V : Section1.ClassFunction G}
    (hAspan : integerSpan R A)
    (hBspan : integerSpan R B)
    (hUorth : orthogonalToFinset R U)
    (hVorth : orthogonalToFinset R V)
    (hEq : A - U = B - V) :
    A = B := by
  have hdiff_span : integerSpan R (A - B) :=
    integerSpan_sub_pf57 hAspan hBspan
  have hdiff_orth : orthogonalToFinset R (A - B) := by
    intro ψ hψ
    have hpoint : A - B = U - V := by
      ext g
      have hEqg := congrArg (fun f : Section1.ClassFunction G => f g) hEq
      change A g - U g = B g - V g at hEqg
      calc
        (A - B) g = A g - B g := rfl
        _ = (A g - U g) + (U g - B g) := by ring
        _ = (B g - V g) + (U g - B g) := by rw [hEqg]
        _ = U g - V g := by ring
        _ = (U - V) g := rfl
    rw [hpoint, scalarProduct_sub_left_pf57]
    simp [hUorth hψ, hVorth hψ]
  have hzero : A - B = 0 :=
    integerSpan_eq_zero_of_orthogonal_pf57 hR hdiff_span hdiff_orth
  ext g
  have hzero_g := congrArg (fun f : Section1.ClassFunction G => f g) hzero
  change A g - B g = 0 at hzero_g
  exact sub_eq_zero.mp hzero_g

private theorem eq_of_self_and_cross_pf57
    {G : Type*} [Group G] [Finite G]
    {A B : Section1.ClassFunction G}
    (hAA : Section1.scalarProduct G A A = Section1.scalarProduct G A B)
    (hBB : Section1.scalarProduct G B B = Section1.scalarProduct G A B)
    (hBA : Section1.scalarProduct G B A = Section1.scalarProduct G A B) :
    A = B := by
  apply sub_eq_zero.mp
  apply cfNormSq_eq_zero_pf57
  unfold cfNormSq
  rw [scalarProduct_sub_left_pf57, scalarProduct_sub_right_pf57, scalarProduct_sub_right_pf57]
  rw [hAA, hBB, hBA]
  simp

private theorem scalarProduct_self_eq_cfNormSq_of_subsetSum_pf57
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R)
    {φ : Section1.ClassFunction G}
    (hsubset : isSubsetSumOf R φ) :
    Section1.scalarProduct G φ φ = (cfNormSq φ : ℂ) := by
  rcases hsubset with ⟨E, hE, rfl⟩
  have hvirt :
      Theory.Character.IsVirtualCharacter (Finset.sum E fun ψ => ψ) := by
    exact isVirtualCharacter_finset_sum_pf57 E (fun ψ => ψ)
      (fun ψ hψ => isVirtualCharacter_of_signedIrreducible_pf57 (hR.1 _ (hE hψ)))
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hvirt hvirt with ⟨n, hn⟩
  have hnorm : cfNormSq (Finset.sum E fun ψ => ψ) = (n : ℝ) := by
    unfold cfNormSq
    rw [hn]
    simp
  calc
    Section1.scalarProduct G (Finset.sum E fun ψ => ψ) (Finset.sum E fun ψ => ψ) = (n : ℂ) := hn
    _ = (cfNormSq (Finset.sum E fun ψ => ψ) : ℂ) := by simp [hnorm]

private theorem integerSpan_of_subsetSum_pf57
    {H : Type*} [Group H]
    {R : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H}
    (hsubset : isSubsetSumOf R φ) :
    integerSpan R φ := by
  classical
  rcases hsubset with ⟨E, hEsub, rfl⟩
  let μE : E → Section1.ClassFunction H := fun ψ => (ψ : Section1.ClassFunction H)
  let oneE : Section1.CoeffVector E := fun _ => 1
  have hsumE : Section1.evalCoeff μE oneE = Finset.sum E fun ψ => ψ := by
    ext g
    simp [Section1.evalCoeff, μE, oneE]
    simpa using (Finset.sum_attach E fun c : Section1.ClassFunction H => c g)
  refine integerSpan_mono_pf57 hEsub ?_
  exact ⟨oneE, hsumE.symm⟩

private theorem subsetSum_self_eq_card_pf57
    {G : Type*} [Group G] [Finite G]
    {R E : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R)
    (hEsub : E ⊆ R) :
    Section1.scalarProduct G (Finset.sum E fun ψ => ψ)
        (Finset.sum E fun ψ => ψ) = (E.card : ℂ) := by
  classical
  let μE : E → Section1.ClassFunction G := fun ψ => (ψ : Section1.ClassFunction G)
  let oneE : Section1.CoeffVector E := fun _ => 1
  have hμEorth :
      ∀ a b : E,
        Section1.scalarProduct G (μE a) (μE b) = if a = b then 1 else 0 := by
    intro a b
    exact scalarProduct_eq_ite_of_signedOrthonormalFinset_pf57
      ⟨fun φ hφ => hR.1 _ (hEsub hφ),
        fun φ ψ hφ hψ hne => hR.2 (hEsub hφ) (hEsub hψ) hne⟩ a b
  have hsumE : Section1.evalCoeff μE oneE = Finset.sum E fun ψ => ψ := by
    ext g
    simp [Section1.evalCoeff, μE, oneE]
    simpa using (Finset.sum_attach E fun c : Section1.ClassFunction G => c g)
  calc
    Section1.scalarProduct G (Finset.sum E fun ψ => ψ) (Finset.sum E fun ψ => ψ)
        = (Section1.coeffDot oneE oneE : ℂ) := by
            rw [← hsumE]
            simpa using
              scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf57 μE hμEorth oneE oneE
    _ = (E.card : ℂ) := by
          simp [Section1.coeffDot, oneE]

private theorem isVirtualCharacter_of_subsetSum_pf57
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R)
    {φ : Section1.ClassFunction G}
    (hsubset : isSubsetSumOf R φ) :
    Theory.Character.IsVirtualCharacter φ := by
  rcases hsubset with ⟨E, hEsub, rfl⟩
  exact isVirtualCharacter_finset_sum_pf57 E (fun ψ => ψ)
    (fun ψ hψ => isVirtualCharacter_of_signedIrreducible_pf57 (hR.1 _ (hEsub hψ)))

private theorem map_evalCoeff_pf57
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

private theorem scalarProduct_evalCoeff_eq_of_gram_eq_pf57
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

private theorem finset_eq_pair_of_card_two_of_conj_stable_pf57
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L))
    (h52a : hypothesis_5_2_a_statement S)
    (X : S)
    (hcard2 : S.card = 2) :
    S = ({(X : Section1.ClassFunction L),
      Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
      Finset (Section1.ClassFunction L)) := by
  classical
  let pair :
      Finset (Section1.ClassFunction L) :=
    {(X : Section1.ClassFunction L),
      Section1.conjugateCharacter (X : Section1.ClassFunction L)}
  have hpair_subset : pair ⊆ S := by
    intro χ hχ
    simp [pair] at hχ
    rcases hχ with rfl | rfl
    · exact X.2
    · exact (h52a X).1
  have hpair_card : pair.card = 2 := by
    simp [pair, h52a X]
  have hpair_eq : pair = S := by
    apply Finset.eq_of_subset_of_card_le hpair_subset
    simp [hpair_card, hcard2]
  simpa [pair] using hpair_eq.symm

private theorem pairDiff_memOn_pf57
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (X : S) :
    integerSpanOn S puncturedSet
      ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
  classical
  let χX : Section1.ClassFunction L := X
  let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
  let xbarS : S := ⟨χXbar, (h52a X).1⟩
  refine ⟨?_, ?_⟩
  · refine ⟨Section1.signedBasisDifference 1 xbarS X, ?_⟩
    ext g
    simpa [χX, χXbar, xbarS, Section1.signIntToComplex] using
      (congrArg (fun f : Section1.ClassFunction L => f g)
        (Section1.evalCoeff_signedBasisDifference
          (G := L) (J := S)
          (mu := fun y : S => (y : Section1.ClassFunction L))
          1 xbarS X)).symm
  · apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf57 _).2
    rcases degree_eq_nat_of_isCharacter_pf57 (hsetup.2 X) with ⟨d, hd⟩
    have hdegbar : Section1.degree χXbar = (d : ℂ) := by
      rw [degree_conjugateCharacter_eq_of_isCharacter_pf57 (hsetup.2 X), hd]
    change Section1.degree χX - Section1.degree χXbar = 0
    rw [hd, hdegbar]
    simp

private theorem diff_memOn_of_equal_degree_pf57
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L))
    (X Y : S)
    (hdeg : Section1.degree (X : Section1.ClassFunction L) =
      Section1.degree (Y : Section1.ClassFunction L)) :
    integerSpanOn S puncturedSet
      ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨Section1.signedBasisDifference 1 Y X, ?_⟩
    ext g
    simpa [Section1.signIntToComplex] using
      (congrArg (fun f : Section1.ClassFunction L => f g)
        (Section1.evalCoeff_signedBasisDifference
          (G := L) (J := S)
          (mu := fun Z : S => (Z : Section1.ClassFunction L))
          1 Y X)).symm
  · apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf57 _).2
    change Section1.degree (X : Section1.ClassFunction L) -
      Section1.degree (Y : Section1.ClassFunction L) = 0
    rw [hdeg]
    simp


private theorem card_R_eq_twice_selfNat_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (X : S) :
    ∃ n : ℕ,
      Section1.scalarProduct L (X : Section1.ClassFunction L) (X : Section1.ClassFunction L) =
          (n : ℂ) ∧
        Section1.scalarProduct L
            (Section1.conjugateCharacter (X : Section1.ClassFunction L))
            (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = (n : ℂ) ∧
          (R X).card = 2 * n := by
  classical
  let χX : Section1.ClassFunction L := X
  let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
  have hχXchar : Section1.IsCharacter χX := hsetup.2 X
  rcases Section1.scalarProduct_character_character_eq_nat χX χX hχXchar hχXchar with
    ⟨n, hn⟩
  have hχXbar_self :
      Section1.scalarProduct L χXbar χXbar = (n : ℂ) := by
    calc
      Section1.scalarProduct L χXbar χXbar =
          star (Section1.scalarProduct L χX χX) := by
            simpa [χX, χXbar, conjugateCharacter_involutive_pf57 χX] using
              scalarProduct_conjugate_left_pf57 χX χXbar
      _ = (n : ℂ) := by simp [hn]
  have hχX_Xbar_zero :
      Section1.scalarProduct L χX χXbar = 0 := by
    exact h52c (χ := χX) (ψ := χXbar) X.2 (h52a X).1 (by
      intro hEq
      exact (h52a X).2 hEq)
  have hχXbar_X_zero :
      Section1.scalarProduct L χXbar χX = 0 := scalarProduct_zero_swap_pf57 hχX_Xbar_zero
  let diffX : Section1.ClassFunction L := χX - χXbar
  have hdiffX_memOn :
      integerSpanOn S puncturedSet diffX := by
    simpa [diffX, χX, χXbar] using pairDiff_memOn_pf57 S hsetup h52a X
  rcases h52d X with ⟨hRX, hTdiffX⟩
  let μ : R X → Section1.ClassFunction G := fun r => (r : Section1.ClassFunction G)
  let oneVec : Section1.CoeffVector (R X) := fun _ => 1
  have hμorth :
      ∀ a b : R X,
        Section1.scalarProduct G (μ a) (μ b) = if a = b then 1 else 0 :=
    scalarProduct_eq_ite_of_signedOrthonormalFinset_pf57 hRX
  have hsumEval :
      Section1.evalCoeff μ oneVec = Finset.sum (R X) fun φ => φ := by
    ext g
    simp [Section1.evalCoeff, μ, oneVec]
    simpa using
      (Finset.sum_attach (R X) fun c : Section1.ClassFunction G => c g)
  have htarget_self :
      Section1.scalarProduct G (Finset.sum (R X) fun φ => φ)
          (Finset.sum (R X) fun φ => φ) = ((R X).card : ℂ) := by
    rw [← hsumEval]
    calc
      Section1.scalarProduct G (Section1.evalCoeff μ oneVec) (Section1.evalCoeff μ oneVec) =
          (Section1.coeffDot oneVec oneVec : ℂ) := by
            simpa using
              scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf57 μ hμorth oneVec oneVec
      _ = ((R X).card : ℂ) := by
            simp [Section1.coeffDot, oneVec]
  have hsource_self :
      Section1.scalarProduct L diffX diffX = (2 * n : ℂ) := by
    dsimp [diffX]
    rw [scalarProduct_sub_left_pf57, scalarProduct_sub_right_pf57,
      scalarProduct_sub_right_pf57]
    simp [hn, hχXbar_self, hχX_Xbar_zero, hχXbar_X_zero]
    ring
  have hdiff_self :
      Section1.scalarProduct G (T diffX) (T diffX) =
        Section1.scalarProduct L diffX diffX := by
    exact h52b.1 diffX diffX hdiffX_memOn hdiffX_memOn
  have hcard_cast : ((R X).card : ℂ) = (2 * n : ℂ) := by
    calc
      ((R X).card : ℂ) =
          Section1.scalarProduct G (Finset.sum (R X) fun φ => φ)
            (Finset.sum (R X) fun φ => φ) := by rw [htarget_self]
      _ = Section1.scalarProduct G (T diffX) (T diffX) := by rw [hTdiffX]
      _ = Section1.scalarProduct L diffX diffX := hdiff_self
      _ = (2 * n : ℂ) := hsource_self
  refine ⟨n, hn, hχXbar_self, ?_⟩
  exact_mod_cast hcard_cast

private theorem pair_case_image_split_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (X : S) :
    ∃ Xbig Xbarimg : Section1.ClassFunction G,
      Theory.Character.IsVirtualCharacter Xbig ∧
        Theory.Character.IsVirtualCharacter Xbarimg ∧
          Section1.scalarProduct G Xbig Xbig =
            Section1.scalarProduct L (X : Section1.ClassFunction L) (X : Section1.ClassFunction L) ∧
          Section1.scalarProduct G Xbarimg Xbarimg =
            Section1.scalarProduct L
              (Section1.conjugateCharacter (X : Section1.ClassFunction L))
              (Section1.conjugateCharacter (X : Section1.ClassFunction L)) ∧
          Section1.scalarProduct G Xbig Xbarimg = 0 ∧
            Section1.scalarProduct G Xbarimg Xbig = 0 ∧
              Xbig - Xbarimg =
                T ((X : Section1.ClassFunction L) -
                  Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
  classical
  let χX : Section1.ClassFunction L := X
  let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
  rcases card_R_eq_twice_selfNat_pf57 S T R hsetup h52a h52b h52c h52d X with
    ⟨n, hn, hχXbar_self, hcardR⟩
  rcases h52d X with ⟨hRX, hTdiffX⟩
  have hn_le : n ≤ (R X).card := by
    rw [hcardR]
    omega
  obtain ⟨E, hE_mem⟩ := Finset.powersetCard_nonempty_of_le hn_le
  have hEsub : E ⊆ R X := (Finset.mem_powersetCard.mp hE_mem).1
  have hEcard : E.card = n := (Finset.mem_powersetCard.mp hE_mem).2
  let Ecomp : Finset (Section1.ClassFunction G) := (R X) \ E
  have hEcomp_subset : Ecomp ⊆ R X := Finset.sdiff_subset
  have hEcomp_card : Ecomp.card = n := by
    dsimp [Ecomp]
    rw [Finset.card_sdiff_of_subset hEsub, hEcard, hcardR]
    omega
  let Xbig : Section1.ClassFunction G := Finset.sum E fun φ => φ
  let Xbarimg : Section1.ClassFunction G := -Finset.sum Ecomp fun φ => φ
  have hXbig_subset : isSubsetSumOf (R X) Xbig := by
    exact ⟨E, hEsub, rfl⟩
  have hE_Ecomp_orth : orthogonalFinsets E Ecomp := by
    intro φ ψ hφ hψ
    have hφR : φ ∈ R X := hEsub hφ
    have hψR : ψ ∈ R X := (Finset.mem_sdiff.mp hψ).1
    have hφneψ : φ ≠ ψ := by
      intro hEq
      exact (Finset.mem_sdiff.mp hψ).2 (hEq ▸ hφ)
    exact hRX.2 hφR hψR hφneψ
  have hXbig_subset_E : isSubsetSumOf E Xbig := ⟨E, subset_rfl, rfl⟩
  have hXbig_orth_Ecomp : orthogonalToFinset Ecomp Xbig :=
    orthogonalToFinset_of_subsetSum_of_orthogonalFinsets_pf57 hXbig_subset_E hE_Ecomp_orth
  let μE : E → Section1.ClassFunction G := fun r => (r : Section1.ClassFunction G)
  let μEcomp : Ecomp → Section1.ClassFunction G := fun r => (r : Section1.ClassFunction G)
  let oneE : Section1.CoeffVector E := fun _ => 1
  let oneEcomp : Section1.CoeffVector Ecomp := fun _ => 1
  have hsumE :
      Section1.evalCoeff μE oneE = Finset.sum E fun φ => φ := by
    ext g
    simp [Section1.evalCoeff, μE, oneE]
    simpa using (Finset.sum_attach E fun c : Section1.ClassFunction G => c g)
  have hsumEcomp :
      Section1.evalCoeff μEcomp oneEcomp = Finset.sum Ecomp fun φ => φ := by
    ext g
    simp [Section1.evalCoeff, μEcomp, oneEcomp]
    simpa using (Finset.sum_attach Ecomp fun c : Section1.ClassFunction G => c g)
  have hXbarimg_eq_negEval :
      Xbarimg = (-1 : ℂ) • Section1.evalCoeff μEcomp oneEcomp := by
    dsimp [Xbarimg]
    rw [← hsumEcomp]
    simp
  have hμEorth :
      ∀ a b : E,
        Section1.scalarProduct G (μE a) (μE b) = if a = b then 1 else 0 := by
    intro a b
    exact scalarProduct_eq_ite_of_signedOrthonormalFinset_pf57
      ⟨fun φ hφ => hRX.1 _ (hEsub hφ),
        fun φ ψ hφ hψ hne => hRX.2 (hEsub hφ) (hEsub hψ) hne⟩ a b
  have hμEcomporth :
      ∀ a b : Ecomp,
        Section1.scalarProduct G (μEcomp a) (μEcomp b) = if a = b then 1 else 0 := by
    intro a b
    exact scalarProduct_eq_ite_of_signedOrthonormalFinset_pf57
      ⟨fun φ hφ => hRX.1 _ (hEcomp_subset hφ),
        fun φ ψ hφ hψ hne => hRX.2 (hEcomp_subset hφ) (hEcomp_subset hψ) hne⟩ a b
  have hXbig_self :
      Section1.scalarProduct G Xbig Xbig =
        Section1.scalarProduct L χX χX := by
    calc
      Section1.scalarProduct G Xbig Xbig =
          Section1.scalarProduct G (Section1.evalCoeff μE oneE) (Section1.evalCoeff μE oneE) := by
            rw [hsumE]
      _ = (Section1.coeffDot oneE oneE : ℂ) := by
            simpa using
              scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf57 μE hμEorth oneE oneE
      _ = (E.card : ℂ) := by
            simp [Section1.coeffDot, oneE]
      _ = (n : ℂ) := by simp [hEcard]
      _ = Section1.scalarProduct L χX χX := by simpa [χX] using hn.symm
  have hXbarimg_self :
      Section1.scalarProduct G Xbarimg Xbarimg =
        Section1.scalarProduct L χXbar χXbar := by
    calc
      Section1.scalarProduct G Xbarimg Xbarimg =
          Section1.scalarProduct G (Section1.evalCoeff μEcomp oneEcomp)
            (Section1.evalCoeff μEcomp oneEcomp) := by
            rw [hXbarimg_eq_negEval, Section1.scalarProduct_smul_left,
              Section1.scalarProduct_smul_right]
            simp
      _ = (Section1.coeffDot oneEcomp oneEcomp : ℂ) := by
            simpa using
              scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf57
                μEcomp hμEcomporth oneEcomp oneEcomp
      _ = (Ecomp.card : ℂ) := by
            simp [Section1.coeffDot, oneEcomp]
      _ = (n : ℂ) := by simp [hEcomp_card]
      _ = Section1.scalarProduct L χXbar χXbar := by simpa [χXbar] using hχXbar_self.symm
  have hXbig_Xbar_zero :
      Section1.scalarProduct G Xbig Xbarimg = 0 := by
    rw [hXbarimg_eq_negEval, Section1.scalarProduct_smul_right]
    simp [orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
      μEcomp (fun r => hXbig_orth_Ecomp r.2) oneEcomp]
  have hXbar_Xbig_zero :
      Section1.scalarProduct G Xbarimg Xbig = 0 :=
    scalarProduct_zero_swap_pf57 hXbig_Xbar_zero
  have hsumSplit :
      Finset.sum (R X) (fun φ => φ) =
        Finset.sum E (fun φ => φ) + Finset.sum Ecomp (fun φ => φ) := by
    simpa [Ecomp, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_sdiff hEsub (f := fun φ : Section1.ClassFunction G => φ)).symm
  refine ⟨Xbig, Xbarimg, ?_, ?_, hXbig_self, hXbarimg_self, hXbig_Xbar_zero,
    hXbar_Xbig_zero, ?_⟩
  · dsimp [Xbig]
    exact isVirtualCharacter_finset_sum_pf57 E (fun φ => φ)
      (fun φ hφ => isVirtualCharacter_of_signedIrreducible_pf57 (hRX.1 _ (hEsub hφ)))
  · dsimp [Xbarimg]
    simpa using Section3.isVirtualCharacter_neg
      (isVirtualCharacter_finset_sum_pf57 Ecomp (fun φ => φ)
        (fun φ hφ => isVirtualCharacter_of_signedIrreducible_pf57 (hRX.1 _ (hEcomp_subset hφ))))
  · calc
      Xbig - Xbarimg =
          Finset.sum E (fun φ => φ) + Finset.sum Ecomp (fun φ => φ) := by
            dsimp [Xbig, Xbarimg]
            abel
      _ = Finset.sum (R X) fun φ => φ := by rw [hsumSplit]
      _ = T (χX - χXbar) := by rw [← hTdiffX]
      _ = T ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
              simp [χX, χXbar]

private theorem complement_image_of_subsetSum_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (X : S)
    {Xbig : Section1.ClassFunction G}
    (hXbig_subset : isSubsetSumOf (R X) Xbig)
    (hXbig_self :
      Section1.scalarProduct G Xbig Xbig =
        Section1.scalarProduct L (X : Section1.ClassFunction L)
          (X : Section1.ClassFunction L)) :
    ∃ Xbarimg : Section1.ClassFunction G,
      Theory.Character.IsVirtualCharacter Xbarimg ∧
        integerSpan (R X) Xbarimg ∧
          Section1.scalarProduct G Xbarimg Xbarimg =
            Section1.scalarProduct L
              (Section1.conjugateCharacter (X : Section1.ClassFunction L))
                (Section1.conjugateCharacter (X : Section1.ClassFunction L)) ∧
            Section1.scalarProduct G Xbig Xbarimg = 0 ∧
              Section1.scalarProduct G Xbarimg Xbig = 0 ∧
                Xbig - Xbarimg =
                  T ((X : Section1.ClassFunction L) -
                    Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
  classical
  let χX : Section1.ClassFunction L := X
  let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
  rcases card_R_eq_twice_selfNat_pf57 S T R hsetup h52a h52b h52c h52d X with
    ⟨n, hn, hχXbar_self, hcardR⟩
  rcases h52d X with ⟨hRX, hTdiffX⟩
  rcases hXbig_subset with ⟨E, hEsub, rfl⟩
  have hEcard_cast : (E.card : ℂ) = (n : ℂ) := by
    calc
      (E.card : ℂ) =
          Section1.scalarProduct G (Finset.sum E fun ψ => ψ) (Finset.sum E fun ψ => ψ) := by
            symm
            exact subsetSum_self_eq_card_pf57 hRX hEsub
      _ = Section1.scalarProduct L χX χX := hXbig_self
      _ = (n : ℂ) := hn
  have hEcard : E.card = n := by
    exact_mod_cast hEcard_cast
  let Ecomp : Finset (Section1.ClassFunction G) := (R X) \ E
  have hEcomp_subset : Ecomp ⊆ R X := Finset.sdiff_subset
  have hEcomp_card : Ecomp.card = n := by
    dsimp [Ecomp]
    rw [Finset.card_sdiff_of_subset hEsub, hEcard, hcardR]
    omega
  let Xbarimg : Section1.ClassFunction G := -Finset.sum Ecomp fun ψ => ψ
  have hE_Ecomp_orth : orthogonalFinsets E Ecomp := by
    intro φ ψ hφ hψ
    have hφR : φ ∈ R X := hEsub hφ
    have hψR : ψ ∈ R X := (Finset.mem_sdiff.mp hψ).1
    have hφneψ : φ ≠ ψ := by
      intro hEq
      exact (Finset.mem_sdiff.mp hψ).2 (hEq ▸ hφ)
    exact hRX.2 hφR hψR hφneψ
  have hXbig_orth_Ecomp :
      orthogonalToFinset Ecomp (Finset.sum E fun ψ => ψ) :=
    orthogonalToFinset_of_subsetSum_of_orthogonalFinsets_pf57
      ⟨E, subset_rfl, rfl⟩ hE_Ecomp_orth
  let μEcomp : Ecomp → Section1.ClassFunction G := fun ψ => (ψ : Section1.ClassFunction G)
  let oneEcomp : Section1.CoeffVector Ecomp := fun _ => 1
  have hsumEcomp :
      Section1.evalCoeff μEcomp oneEcomp = Finset.sum Ecomp fun ψ => ψ := by
    ext g
    simp [Section1.evalCoeff, μEcomp, oneEcomp]
    simpa using (Finset.sum_attach Ecomp fun c : Section1.ClassFunction G => c g)
  have hXbarimg_virt : Theory.Character.IsVirtualCharacter Xbarimg := by
    dsimp [Xbarimg]
    simpa using Section3.isVirtualCharacter_neg
      (isVirtualCharacter_finset_sum_pf57 Ecomp (fun ψ => ψ)
        (fun ψ hψ => isVirtualCharacter_of_signedIrreducible_pf57 (hRX.1 _ (hEcomp_subset hψ))))
  have hEcomp_subsetSum :
      isSubsetSumOf (R X) (Finset.sum Ecomp fun ψ => ψ) := ⟨Ecomp, hEcomp_subset, rfl⟩
  have hXbarimg_span : integerSpan (R X) Xbarimg := by
    dsimp [Xbarimg]
    simpa using integerSpan_neg_pf57
      (integerSpan_of_subsetSum_pf57 hEcomp_subsetSum)
  have hXbarimg_eq_negEval :
      Xbarimg = (-1 : ℂ) • Section1.evalCoeff μEcomp oneEcomp := by
    dsimp [Xbarimg]
    rw [← hsumEcomp]
    simp
  have hXbarimg_self :
      Section1.scalarProduct G Xbarimg Xbarimg =
        Section1.scalarProduct L χXbar χXbar := by
    calc
      Section1.scalarProduct G Xbarimg Xbarimg =
          Section1.scalarProduct G (Section1.evalCoeff μEcomp oneEcomp)
            (Section1.evalCoeff μEcomp oneEcomp) := by
              rw [hXbarimg_eq_negEval, Section1.scalarProduct_smul_left,
                Section1.scalarProduct_smul_right]
              simp
      _ = (Section1.coeffDot oneEcomp oneEcomp : ℂ) := by
            simpa using
              scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf57
                μEcomp
                (fun a b =>
                  scalarProduct_eq_ite_of_signedOrthonormalFinset_pf57
                    ⟨fun φ hφ => hRX.1 _ (hEcomp_subset hφ),
                      fun φ ψ hφ hψ hne => hRX.2 (hEcomp_subset hφ) (hEcomp_subset hψ) hne⟩ a b)
                oneEcomp oneEcomp
      _ = (Ecomp.card : ℂ) := by
            simp [Section1.coeffDot, oneEcomp]
      _ = (n : ℂ) := by simp [hEcomp_card]
      _ = Section1.scalarProduct L χXbar χXbar := by simpa [χXbar] using hχXbar_self.symm
  have hXbig_Xbar_zero :
      Section1.scalarProduct G (Finset.sum E fun ψ => ψ) Xbarimg = 0 := by
    rw [hXbarimg_eq_negEval, Section1.scalarProduct_smul_right]
    simp [orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
      μEcomp (fun ψ => hXbig_orth_Ecomp ψ.2) oneEcomp]
  have hXbar_Xbig_zero :
      Section1.scalarProduct G Xbarimg (Finset.sum E fun ψ => ψ) = 0 :=
    scalarProduct_zero_swap_pf57 hXbig_Xbar_zero
  have hsumSplit :
      Finset.sum (R X) (fun ψ => ψ) =
        Finset.sum E (fun ψ => ψ) + Finset.sum Ecomp (fun ψ => ψ) := by
    simpa [Ecomp, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_sdiff hEsub (f := fun ψ : Section1.ClassFunction G => ψ)).symm
  refine ⟨Xbarimg, hXbarimg_virt, hXbarimg_span, hXbarimg_self, ?_, hXbar_Xbig_zero, ?_⟩
  · simpa using hXbig_Xbar_zero
  · calc
      Finset.sum E (fun ψ => ψ) - Xbarimg =
          Finset.sum E (fun ψ => ψ) + Finset.sum Ecomp (fun ψ => ψ) := by
            dsimp [Xbarimg]
            abel
      _ = Finset.sum (R X) fun ψ => ψ := by rw [hsumSplit]
      _ = T (χX - χXbar) := by rw [← hTdiffX]
      _ = T ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
              simp [χX, χXbar]

private theorem exists_third_member_of_card_ne_two_pf57
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L))
    (_hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (X : S)
    (hcard2 : S.card ≠ 2) :
    ∃ X1 : S,
      (X1 : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L) ∧
        (X1 : Section1.ClassFunction L) ≠
          Section1.conjugateCharacter (X : Section1.ClassFunction L) := by
  classical
  let χX : Section1.ClassFunction L := X
  let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
  let pair :
      Finset (Section1.ClassFunction L) :=
    {χX, χXbar}
  have hpair_subset : pair ⊆ S := by
    intro ψ hψ
    simp [pair, χX, χXbar] at hψ
    rcases hψ with rfl | rfl
    · exact X.2
    · exact (h52a X).1
  have hpair_card : pair.card = 2 := by
    simp [pair, χX, χXbar, h52a X]
  by_contra hnone
  have hS_subset_pair : S ⊆ pair := by
    intro ψ hψ
    by_contra hψpair
    have hψneX : ψ ≠ χX := by
      intro hEq
      exact hψpair (hEq ▸ by simp [pair])
    have hψneXbar : ψ ≠ χXbar := by
      intro hEq
      exact hψpair (hEq ▸ by simp [pair])
    exact hnone ⟨⟨ψ, hψ⟩, hψneX, hψneXbar⟩
  have hS_eq_pair : S = pair := by
    exact Finset.Subset.antisymm hS_subset_pair hpair_subset
  exact hcard2 (by simpa [hS_eq_pair] using hpair_card)

private theorem theorem_5_7_general_source_data_pf57
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52c : hypothesis_5_2_c_statement S)
  (hcard2 : S.card ≠ 2)
  (hdeg : ∀ X Y : S,
      Section1.degree (X : Section1.ClassFunction L) =
        Section1.degree (Y : Section1.ClassFunction L)) :
    ∃ X X1 : S,
      (X1 : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L) ∧
        (X1 : Section1.ClassFunction L) ≠
          Section1.conjugateCharacter (X : Section1.ClassFunction L) ∧
        integerSpanOn S puncturedSet
          ((X : Section1.ClassFunction L) - (X1 : Section1.ClassFunction L)) ∧
        integerSpanOn S puncturedSet
          ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) ∧
        Section1.scalarProduct L
          (X : Section1.ClassFunction L) (X1 : Section1.ClassFunction L) = 0 ∧
        Section1.scalarProduct L
          (Section1.conjugateCharacter (X : Section1.ClassFunction L))
          (X1 : Section1.ClassFunction L) = 0 := by
  classical
  rcases hsetup.1 with ⟨X0, hX0⟩
  let X : S := ⟨X0, hX0⟩
  rcases exists_third_member_of_card_ne_two_pf57 S hsetup h52a X hcard2 with
    ⟨X1, hX1_ne_X, hX1_ne_Xbar⟩
  let Xbar : S :=
    ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩
  have hdiff_X_X1 :
      integerSpanOn S puncturedSet
        ((X : Section1.ClassFunction L) - (X1 : Section1.ClassFunction L)) :=
    diff_memOn_of_equal_degree_pf57 S X X1 (hdeg X X1)
  have hdiff_X_Xbar :
      integerSpanOn S puncturedSet
        ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)) :=
    pairDiff_memOn_pf57 S hsetup h52a X
  have hX_X1_zero :
      Section1.scalarProduct L
        (X : Section1.ClassFunction L) (X1 : Section1.ClassFunction L) = 0 :=
    h52c X.2 X1.2 hX1_ne_X.symm
  have hXbar_X1_zero :
      Section1.scalarProduct L
        (Section1.conjugateCharacter (X : Section1.ClassFunction L))
        (X1 : Section1.ClassFunction L) = 0 := by
    exact h52c Xbar.2 X1.2 (by
      intro hEq
      exact hX1_ne_Xbar (by simpa [Xbar] using hEq.symm))
  exact ⟨X, X1, hX1_ne_X, hX1_ne_Xbar, hdiff_X_X1, hdiff_X_Xbar,
    hX_X1_zero, hXbar_X1_zero⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
public theorem theorem_5_4_projection_data_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (h52e : hypothesis_5_2_e_statement S R)
    (X : S)
    (ψ : Section1.ClassFunction L)
    (hψ_span : integerSpan S ψ)
    (hdiff_X_ψ : integerSpanOn S puncturedSet
      ((X : Section1.ClassFunction L) - ψ))
    (hdiff_X_Xbar : integerSpanOn S puncturedSet
      ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)))
    (hX_ψ_zero : Section1.scalarProduct L
      (X : Section1.ClassFunction L) ψ = 0)
    (hXbar_ψ_zero : Section1.scalarProduct L
      (Section1.conjugateCharacter (X : Section1.ClassFunction L)) ψ = 0) :
    ∃ Xbig Y : Section1.ClassFunction G,
      integerSpan (R X) Xbig ∧
        orthogonalToFinset (R X) Y ∧
        T ((X : Section1.ClassFunction L) - ψ) = Xbig - Y ∧
        cfNormSq Xbig ≥ cfNormSq (X : Section1.ClassFunction L) ∧
        (cfNormSq Y ≥ cfNormSq ψ →
          cfNormSq Xbig = cfNormSq (X : Section1.ClassFunction L) ∧
            cfNormSq Y = cfNormSq ψ ∧
              isSubsetSumOf (R X) Xbig) := by
  classical
  let diffψ : Section1.ClassFunction L :=
    (X : Section1.ClassFunction L) - ψ
  let diffX : Section1.ClassFunction L :=
    (X : Section1.ClassFunction L) -
      Section1.conjugateCharacter (X : Section1.ClassFunction L)
  let pairDiff : Finset (Section1.ClassFunction L) := {diffψ, diffX}
  have hpairDiff_gen :
      ∀ φ : Section1.ClassFunction L, φ ∈ pairDiff → integerSpanOn S puncturedSet φ := by
    intro φ hφ
    simp [pairDiff] at hφ
    rcases hφ with rfl | rfl
    · simpa [diffψ] using hdiff_X_ψ
    · simpa [diffX] using hdiff_X_Xbar
  have hTpairIso :
      isCFLinearIsometryOnSpan pairDiff T := by
    intro φ ψ' hφ hψ'
    exact h52b.1 φ ψ'
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiff)
        (A := puncturedSet) hpairDiff_gen hφ)
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiff)
        (A := puncturedSet) hpairDiff_gen hψ')
  have hTpairVirt :
      mapsIntegerSpanToVirtualCharacters pairDiff T := by
    intro φ hφ
    exact (h52b.2 φ
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiff)
        (A := puncturedSet) hpairDiff_gen hφ)).1
  have hTdiffψ_virt :
      Theory.Character.IsVirtualCharacter (T diffψ) :=
    (h52b.2 diffψ (by simpa [diffψ] using hdiff_X_ψ)).1
  rcases h52d X with ⟨hRX, hTdiffX⟩
  rcases orthogonal_projection_decomposition_pf57 (R := R X) hRX hTdiffψ_virt with
    ⟨Xbig, Y, hXbig_span, hY_orth, hTdiffψ_eq⟩
  have h54 :
      cfNormSq Xbig ≥ cfNormSq (X : Section1.ClassFunction L) ∧
        (cfNormSq Y ≥ cfNormSq ψ →
          cfNormSq Xbig = cfNormSq (X : Section1.ClassFunction L) ∧
            cfNormSq Y = cfNormSq ψ ∧
              isSubsetSumOf (R X) Xbig) := by
    exact theorem_5_4 S T R hsetup h52a h52b h52c h52d h52e X ψ
      hψ_span hX_ψ_zero hXbar_ψ_zero T hTpairIso hTpairVirt
      (by simpa [diffX] using hTdiffX) Xbig Y
      hXbig_span hY_orth (by simpa [diffψ] using hTdiffψ_eq)
  exact ⟨Xbig, Y, hXbig_span, hY_orth, by simpa [diffψ] using hTdiffψ_eq,
    h54.1, h54.2⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
private theorem theorem_5_7_projection_data_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (h52e : hypothesis_5_2_e_statement S R)
    (X X1 : S)
    (hdiff_X_X1 : integerSpanOn S puncturedSet
      ((X : Section1.ClassFunction L) - (X1 : Section1.ClassFunction L)))
    (hdiff_X_Xbar : integerSpanOn S puncturedSet
      ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)))
    (hX_X1_zero : Section1.scalarProduct L
      (X : Section1.ClassFunction L) (X1 : Section1.ClassFunction L) = 0)
    (hXbar_X1_zero : Section1.scalarProduct L
      (Section1.conjugateCharacter (X : Section1.ClassFunction L))
      (X1 : Section1.ClassFunction L) = 0) :
    ∃ Xbig Y : Section1.ClassFunction G,
      integerSpan (R X) Xbig ∧
        orthogonalToFinset (R X) Y ∧
        T ((X : Section1.ClassFunction L) - (X1 : Section1.ClassFunction L)) =
          Xbig - Y ∧
        cfNormSq Xbig ≥ cfNormSq (X : Section1.ClassFunction L) ∧
        (cfNormSq Y ≥ cfNormSq (X1 : Section1.ClassFunction L) →
          cfNormSq Xbig = cfNormSq (X : Section1.ClassFunction L) ∧
            cfNormSq Y = cfNormSq (X1 : Section1.ClassFunction L) ∧
              isSubsetSumOf (R X) Xbig) := by
  classical
  let diffψ : Section1.ClassFunction L :=
    (X : Section1.ClassFunction L) - (X1 : Section1.ClassFunction L)
  let diffX : Section1.ClassFunction L :=
    (X : Section1.ClassFunction L) -
      Section1.conjugateCharacter (X : Section1.ClassFunction L)
  let pairDiff : Finset (Section1.ClassFunction L) := {diffψ, diffX}
  have hpairDiff_gen :
      ∀ φ : Section1.ClassFunction L, φ ∈ pairDiff → integerSpanOn S puncturedSet φ := by
    intro φ hφ
    simp [pairDiff] at hφ
    rcases hφ with rfl | rfl
    · simpa [diffψ] using hdiff_X_X1
    · simpa [diffX] using hdiff_X_Xbar
  have hTpairIso :
      isCFLinearIsometryOnSpan pairDiff T := by
    intro φ ψ hφ hψ
    exact h52b.1 φ ψ
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiff)
        (A := puncturedSet) hpairDiff_gen hφ)
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiff)
        (A := puncturedSet) hpairDiff_gen hψ)
  have hTpairVirt :
      mapsIntegerSpanToVirtualCharacters pairDiff T := by
    intro φ hφ
    exact (h52b.2 φ
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiff)
        (A := puncturedSet) hpairDiff_gen hφ)).1
  have hTdiffψ_virt :
      Theory.Character.IsVirtualCharacter (T diffψ) :=
    (h52b.2 diffψ (by simpa [diffψ] using hdiff_X_X1)).1
  rcases h52d X with ⟨hRX, hTdiffX⟩
  rcases orthogonal_projection_decomposition_pf57 (R := R X) hRX hTdiffψ_virt with
    ⟨Xbig, Y, hXbig_span, hY_orth, hTdiffψ_eq⟩
  have h54 :
      cfNormSq Xbig ≥ cfNormSq (X : Section1.ClassFunction L) ∧
        (cfNormSq Y ≥ cfNormSq (X1 : Section1.ClassFunction L) →
          cfNormSq Xbig = cfNormSq (X : Section1.ClassFunction L) ∧
            cfNormSq Y = cfNormSq (X1 : Section1.ClassFunction L) ∧
              isSubsetSumOf (R X) Xbig) := by
    exact theorem_5_4 S T R hsetup h52a h52b h52c h52d h52e X
      (X1 : Section1.ClassFunction L)
      (integerSpan_of_mem_pf57 S X1.2)
      hX_X1_zero hXbar_X1_zero T hTpairIso hTpairVirt
      (by simpa [diffX] using hTdiffX) Xbig Y
      hXbig_span hY_orth (by simpa [diffψ] using hTdiffψ_eq)
  exact ⟨Xbig, Y, hXbig_span, hY_orth, by simpa [diffψ] using hTdiffψ_eq,
    h54.1, h54.2⟩


set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
private theorem diff_image_split_of_equal_degree_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (h52e : hypothesis_5_2_e_statement S R)
    (hdeg : ∀ X Y : S,
      Section1.degree (X : Section1.ClassFunction L) =
        Section1.degree (Y : Section1.ClassFunction L))
    (X Y : S)
    (hXY : (Y : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L))
    (hYneXbar : (Y : Section1.ClassFunction L) ≠
      Section1.conjugateCharacter (X : Section1.ClassFunction L)) :
    ∃ Xbig Yimg : Section1.ClassFunction G,
      integerSpan (R X) Xbig ∧
        integerSpan (R Y) Yimg ∧
          isSubsetSumOf (R X) Xbig ∧
            isSubsetSumOf (R Y) Yimg ∧
              orthogonalToFinset (R Y) Xbig ∧
                orthogonalToFinset (R X) Yimg ∧
                  T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
                    Xbig - Yimg ∧
                    Section1.scalarProduct G Xbig Xbig =
                      Section1.scalarProduct L (X : Section1.ClassFunction L)
                        (X : Section1.ClassFunction L) ∧
                      Section1.scalarProduct G Yimg Yimg =
                        Section1.scalarProduct L (Y : Section1.ClassFunction L)
                          (Y : Section1.ClassFunction L) := by
  classical
  let χX : Section1.ClassFunction L := X
  let χY : Section1.ClassFunction L := Y
  let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
  let χYbar : Section1.ClassFunction L := Section1.conjugateCharacter χY
  have hχXchar : Section1.IsCharacter χX := hsetup.2 X
  have hχYchar : Section1.IsCharacter χY := hsetup.2 Y
  have hdiffXY_memOn :
      integerSpanOn S puncturedSet (χX - χY) := by
    simpa [χX, χY] using diff_memOn_of_equal_degree_pf57 S X Y (hdeg X Y)
  have hdiffYX_memOn :
      integerSpanOn S puncturedSet (χY - χX) := by
    simpa [χX, χY] using diff_memOn_of_equal_degree_pf57 S Y X (hdeg Y X)
  have hdiffX_memOn :
      integerSpanOn S puncturedSet (χX - χXbar) := by
    simpa [χX, χXbar] using pairDiff_memOn_pf57 S hsetup h52a X
  have hdiffY_memOn :
      integerSpanOn S puncturedSet (χY - χYbar) := by
    simpa [χY, χYbar] using pairDiff_memOn_pf57 S hsetup h52a Y
  let pairDiffX : Finset (Section1.ClassFunction L) := {χX - χY, χX - χXbar}
  have hpairDiffX_gen :
      ∀ φ : Section1.ClassFunction L, φ ∈ pairDiffX → integerSpanOn S puncturedSet φ := by
    intro φ hφ
    simp [pairDiffX, χX, χY, χXbar] at hφ
    rcases hφ with rfl | rfl
    · exact hdiffXY_memOn
    · exact hdiffX_memOn
  have hTpairIsoX :
      isCFLinearIsometryOnSpan pairDiffX T := by
    intro φ ψ hφ hψ
    exact h52b.1 φ ψ
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiffX) (A := puncturedSet)
        hpairDiffX_gen hφ)
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiffX) (A := puncturedSet)
        hpairDiffX_gen hψ)
  have hTpairVirtX :
      mapsIntegerSpanToVirtualCharacters pairDiffX T := by
    intro φ hφ
    exact (h52b.2 φ
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiffX) (A := puncturedSet)
        hpairDiffX_gen hφ)).1
  let pairDiffY : Finset (Section1.ClassFunction L) := {χY - χX, χY - χYbar}
  have hpairDiffY_gen :
      ∀ φ : Section1.ClassFunction L, φ ∈ pairDiffY → integerSpanOn S puncturedSet φ := by
    intro φ hφ
    simp [pairDiffY, χX, χY, χYbar] at hφ
    rcases hφ with rfl | rfl
    · exact hdiffYX_memOn
    · exact hdiffY_memOn
  have hTpairIsoY :
      isCFLinearIsometryOnSpan pairDiffY T := by
    intro φ ψ hφ hψ
    exact h52b.1 φ ψ
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiffY) (A := puncturedSet)
        hpairDiffY_gen hφ)
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiffY) (A := puncturedSet)
        hpairDiffY_gen hψ)
  have hTpairVirtY :
      mapsIntegerSpanToVirtualCharacters pairDiffY T := by
    intro φ hφ
    exact (h52b.2 φ
      (integerSpanOn_of_generators_pf57 (S := S) (U := pairDiffY) (A := puncturedSet)
        hpairDiffY_gen hφ)).1
  have hXY_zero :
      Section1.scalarProduct L χX χY = 0 := by
    exact h52c X.2 Y.2 hXY.symm
  have hXbarY_zero :
      Section1.scalarProduct L χXbar χY = 0 := by
    exact h52c (h52a X).1 Y.2 (by
      intro hEq
      exact hYneXbar hEq.symm)
  have hYX_zero :
      Section1.scalarProduct L χY χX = 0 := scalarProduct_zero_swap_pf57 hXY_zero
  have hYXbar_zero :
      Section1.scalarProduct L χY χXbar = 0 := scalarProduct_zero_swap_pf57 hXbarY_zero
  have hYbarX_zero :
      Section1.scalarProduct L χYbar χX = 0 := by
    exact h52c (h52a Y).1 X.2 (by
      intro hEq
      apply hYneXbar
      calc
        χY = Section1.conjugateCharacter χYbar := by
          simpa [χYbar] using (conjugateCharacter_involutive_pf57 χY).symm
        _ = Section1.conjugateCharacter χX := by rw [hEq])
  have hXYbar_zero :
      Section1.scalarProduct L χX χYbar = 0 := scalarProduct_zero_swap_pf57 hYbarX_zero
  have horthYX : orthogonalFinsets (R Y) (R X) := h52e X Y hYX_zero hYXbar_zero
  have horthXY : orthogonalFinsets (R X) (R Y) := h52e Y X hXY_zero hXYbar_zero
  have hηvirt : Theory.Character.IsVirtualCharacter (T (χX - χY)) :=
    (h52b.2 (χX - χY) hdiffXY_memOn).1
  rcases h52d X with ⟨hRX, _hTdiffX⟩
  rcases h52d Y with ⟨hRY, _hTdiffY⟩
  rcases orthogonal_projection_decomposition_pf57 (R := R X) hRX hηvirt with
    ⟨Xbig, remX, hXbig_span, hremX_orthX, hsplitX⟩
  let μX : R X → Section1.ClassFunction G := fun r => (r : Section1.ClassFunction G)
  have hXbig_virt : Theory.Character.IsVirtualCharacter Xbig := by
    rcases hXbig_span with ⟨v, rfl⟩
    exact isVirtualCharacter_evalCoeff_pf57 μX
      (fun r => isVirtualCharacter_of_signedIrreducible_pf57 (hRX.1 _ r.2)) v
  have hremX_eq :
      remX = Xbig - T (χX - χY) := by
    ext g
    have hsplitXg : T (χX - χY) g = Xbig g - remX g := by
      simpa [χX, χY] using congrArg (fun f : Section1.ClassFunction G => f g) hsplitX
    calc
      remX g = Xbig g - (Xbig g - remX g) := by ring
      _ = Xbig g - T (χX - χY) g := by rw [hsplitXg]
  have hremXvirt : Theory.Character.IsVirtualCharacter remX := by
    simpa [hremX_eq] using Section3.isVirtualCharacter_sub hXbig_virt hηvirt
  rcases orthogonal_projection_decomposition_pf57 (R := R Y) hRY hremXvirt with
    ⟨Yimg, Yrem, hYimg_span, hYrem_orthY, hsplitY⟩
  let μY : R Y → Section1.ClassFunction G := fun r => (r : Section1.ClassFunction G)
  have hXbig_orthY : orthogonalToFinset (R Y) Xbig :=
    orthogonalToFinset_of_integerSpan_of_orthogonalFinsets_pf57 hXbig_span horthXY
  have hYimg_orthX : orthogonalToFinset (R X) Yimg :=
    orthogonalToFinset_of_integerSpan_of_orthogonalFinsets_pf57 hYimg_span horthYX
  have hYrem_eq :
      Yrem = Yimg - remX := by
    ext g
    have hsplitYg : remX g = Yimg g - Yrem g := by
      simpa using congrArg (fun f : Section1.ClassFunction G => f g) hsplitY
    calc
      Yrem g = Yimg g - (Yimg g - Yrem g) := by ring
      _ = Yimg g - remX g := by rw [hsplitYg]
  have hYrem_orthX : orthogonalToFinset (R X) Yrem := by
    intro ψ hψ
    rw [hYrem_eq, scalarProduct_sub_left_pf57]
    simp [hYimg_orthX hψ, hremX_orthX hψ]
  have hrestX_orth : orthogonalToFinset (R X) (Yimg - Yrem) :=
    orthogonalToFinset_sub_pf57 hYimg_orthX hYrem_orthX
  have hrestY_orth : orthogonalToFinset (R Y) (Xbig + Yrem) :=
    orthogonalToFinset_add_pf57 hXbig_orthY hYrem_orthY
  have hsplitX' :
      T (χX - χY) = Xbig - (Yimg - Yrem) := by
    rw [hsplitX, hsplitY]
  have hsplitY' :
      T (χY - χX) = Yimg - (Xbig + Yrem) := by
    calc
      T (χY - χX) = -T (χX - χY) := by simp [χX, χY]
      _ = -(Xbig - (Yimg - Yrem)) := by rw [hsplitX']
      _ = Yimg - (Xbig + Yrem) := by abel
  have h54X :=
      theorem_5_4 S T R hsetup h52a h52b h52c h52d h52e X
        Y (integerSpan_of_mem_pf57 S Y.2)
        hXY_zero hXbarY_zero T hTpairIsoX hTpairVirtX rfl
        Xbig (Yimg - Yrem) hXbig_span hrestX_orth hsplitX'
  have h54Y :=
      theorem_5_4 S T R hsetup h52a h52b h52c h52d h52e Y
        X (integerSpan_of_mem_pf57 S X.2)
        hYX_zero hYbarX_zero T hTpairIsoY hTpairVirtY rfl
        Yimg (Xbig + Yrem) hYimg_span hrestY_orth hsplitY'
  have hYimg_ge : cfNormSq Yimg ≥ cfNormSq χY := h54Y.1
  have hXbig_ge : cfNormSq Xbig ≥ cfNormSq χX := h54X.1
  have hYimgYrem_zero :
      Section1.scalarProduct G Yimg Yrem = 0 := by
    rcases hYimg_span with ⟨v, rfl⟩
    exact scalarProduct_zero_swap_pf57
      (orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57 μY
        (fun r => hYrem_orthY r.2) v)
  have hYremYimg_zero :
      Section1.scalarProduct G Yrem Yimg = 0 := scalarProduct_zero_swap_pf57 hYimgYrem_zero
  have hXbigYrem_zero :
      Section1.scalarProduct G Xbig Yrem = 0 := by
    rcases hXbig_span with ⟨v, rfl⟩
    exact scalarProduct_zero_swap_pf57
      (orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57 μX
        (fun r => hYrem_orthX r.2) v)
  have hYremXbig_zero :
      Section1.scalarProduct G Yrem Xbig = 0 := scalarProduct_zero_swap_pf57 hXbigYrem_zero
  have hrestX_ge :
      cfNormSq (Yimg - Yrem) ≥ cfNormSq χY := by
    rw [cfNormSq_sub_eq_add_of_orthogonal_pf57 hYimgYrem_zero hYremYimg_zero]
    have hYrem_nonneg : 0 ≤ cfNormSq Yrem := cfNormSq_nonneg_pf57 Yrem
    linarith
  have h54X' := h54X.2 hrestX_ge
  rcases h54X' with ⟨hXbig_cf, _hrestX_cf, hXbig_subset⟩
  have hrestY_ge :
      cfNormSq (Xbig + Yrem) ≥ cfNormSq χX := by
    rw [cfNormSq_add_eq_add_of_orthogonal_pf57 hXbigYrem_zero hYremXbig_zero]
    have hYrem_nonneg : 0 ≤ cfNormSq Yrem := cfNormSq_nonneg_pf57 Yrem
    linarith
  have h54Y' := h54Y.2 hrestY_ge
  rcases h54Y' with ⟨hYimg_cf, hrestY_cf, hYimg_subset⟩
  have hYrem_cf :
      cfNormSq Yrem = 0 := by
    rw [cfNormSq_add_eq_add_of_orthogonal_pf57 hXbigYrem_zero hYremXbig_zero] at hrestY_cf
    linarith
  have hYrem_zero : Yrem = 0 := cfNormSq_eq_zero_pf57 hYrem_cf
  have hsplit_final :
      T (χX - χY) = Xbig - Yimg := by
    simpa [hYrem_zero] using hsplitX'
  have hXbig_self :
      Section1.scalarProduct G Xbig Xbig = Section1.scalarProduct L χX χX := by
    calc
      Section1.scalarProduct G Xbig Xbig = (cfNormSq Xbig : ℂ) := by
        exact scalarProduct_self_eq_cfNormSq_of_subsetSum_pf57 hRX hXbig_subset
      _ = (cfNormSq χX : ℂ) := by rw [hXbig_cf]
      _ = Section1.scalarProduct L χX χX := by
        symm
        exact scalarProduct_self_eq_cfNormSq_of_character_pf57 hχXchar
  have hYimg_self :
      Section1.scalarProduct G Yimg Yimg = Section1.scalarProduct L χY χY := by
    calc
      Section1.scalarProduct G Yimg Yimg = (cfNormSq Yimg : ℂ) := by
        exact scalarProduct_self_eq_cfNormSq_of_subsetSum_pf57 hRY hYimg_subset
      _ = (cfNormSq χY : ℂ) := by rw [hYimg_cf]
      _ = Section1.scalarProduct L χY χY := by
        symm
        exact scalarProduct_self_eq_cfNormSq_of_character_pf57 hχYchar
  exact ⟨Xbig, Yimg, hXbig_span, hYimg_span, hXbig_subset, hYimg_subset, hXbig_orthY,
    hYimg_orthX, hsplit_final, hXbig_self, hYimg_self⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
private theorem anchored_image_general_case_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (h52e : hypothesis_5_2_e_statement S R)
    (hdeg : ∀ X Y : S,
      Section1.degree (X : Section1.ClassFunction L) =
        Section1.degree (Y : Section1.ClassFunction L))
    (X X1 Y : S)
    {Xbig X1img : Section1.ClassFunction G}
    (hX1_ne_X : (X1 : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L))
    (hX1_ne_Xbar : (X1 : Section1.ClassFunction L) ≠
      Section1.conjugateCharacter (X : Section1.ClassFunction L))
    (hYneX : (Y : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L))
    (hYneXbar : (Y : Section1.ClassFunction L) ≠
      Section1.conjugateCharacter (X : Section1.ClassFunction L))
    (hYneX1 : Y ≠ X1)
    (hYneX1bar : (Y : Section1.ClassFunction L) ≠
      Section1.conjugateCharacter (X1 : Section1.ClassFunction L))
    (hXbig_span : integerSpan (R X) Xbig)
    (hX1img_span : integerSpan (R X1) X1img)
    (hX1img_subset : isSubsetSumOf (R X1) X1img)
    (hX1img_orthX : orthogonalToFinset (R X) X1img)
    (hsplit_X1 :
      T ((X : Section1.ClassFunction L) - (X1 : Section1.ClassFunction L)) =
        Xbig - X1img)
    (hXbig_self :
      Section1.scalarProduct G Xbig Xbig =
        Section1.scalarProduct L (X : Section1.ClassFunction L)
          (X : Section1.ClassFunction L)) :
    ∃ Yimg : Section1.ClassFunction G,
      Theory.Character.IsVirtualCharacter Yimg ∧
        orthogonalToFinset (R X) Yimg ∧
          T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
            Xbig - Yimg ∧
            Section1.scalarProduct G Yimg Yimg =
              Section1.scalarProduct L (Y : Section1.ClassFunction L)
                (Y : Section1.ClassFunction L) := by
  classical
  let χX : Section1.ClassFunction L := X
  let χX1 : Section1.ClassFunction L := X1
  let χX1bar : Section1.ClassFunction L := Section1.conjugateCharacter χX1
  have hXX1_zero :
      Section1.scalarProduct L χX χX1 = 0 := by
    exact h52c X.2 X1.2 hX1_ne_X.symm
  have hX1X_zero :
      Section1.scalarProduct L χX1 χX = 0 := scalarProduct_zero_swap_pf57 hXX1_zero
  have hX1Xbar_zero :
      Section1.scalarProduct L χX1 (Section1.conjugateCharacter χX) = 0 := by
    exact h52c X1.2 (h52a X).1 (by
      intro hEq
      exact hX1_ne_Xbar (by simpa [χX1bar] using hEq))
  have horthX1X : orthogonalFinsets (R X1) (R X) := h52e X X1 hX1X_zero hX1Xbar_zero
  have hXX1bar_zero :
      Section1.scalarProduct L χX χX1bar = 0 := by
    exact h52c X.2 (h52a X1).1 (by
      intro hEq
      have hback := congrArg Section1.conjugateCharacter hEq
      have hEq' : Section1.conjugateCharacter (X : Section1.ClassFunction L) = χX1 := by
        simpa [χX1bar, conjugateCharacter_involutive_pf57] using hback
      exact hX1_ne_Xbar (by simpa [χX1bar] using hEq'.symm))
  have horthXX1 : orthogonalFinsets (R X) (R X1) := h52e X1 X hXX1_zero hXX1bar_zero
  rcases diff_image_split_of_equal_degree_pf57 S T R hsetup h52a h52b h52c h52d
        h52e hdeg X Y hYneX hYneXbar with
    ⟨XbigY, Yimg, hXbigY_span, _hYimg_span, _hXbigY_subset, hYimg_subset,
      _hXbigY_orthY, hYimg_orthX, hsplitY, hXbigY_self, hYimg_self⟩
  have hRY : signedOrthonormalFinset (R Y) := (h52d Y).1
  have hYimg_virt : Theory.Character.IsVirtualCharacter Yimg :=
    isVirtualCharacter_of_subsetSum_pf57 hRY hYimg_subset
  have hXY_zero :
      Section1.scalarProduct L χX (Y : Section1.ClassFunction L) = 0 := by
    exact h52c X.2 Y.2 hYneX.symm
  have hYX_zero :
      Section1.scalarProduct L (Y : Section1.ClassFunction L) χX = 0 :=
    scalarProduct_zero_swap_pf57 hXY_zero
  have hX1Y_zero :
      Section1.scalarProduct L χX1 (Y : Section1.ClassFunction L) = 0 := by
    exact h52c X1.2 Y.2 (by
      intro hEq
      exact hYneX1 (Subtype.ext hEq).symm)
  have hYX1_zero :
      Section1.scalarProduct L (Y : Section1.ClassFunction L) χX1 = 0 :=
    scalarProduct_zero_swap_pf57 hX1Y_zero
  have hX1Ybar_zero :
      Section1.scalarProduct L χX1
          (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) = 0 := by
    exact h52c X1.2 (h52a Y).1 (by
      intro hEq
      have hback := congrArg Section1.conjugateCharacter hEq
      have hEq' : (Y : Section1.ClassFunction L) = χX1bar := by
        simpa [χX1bar, conjugateCharacter_involutive_pf57] using hback.symm
      exact hYneX1bar hEq')
  have hX1barY_zero :
      Section1.scalarProduct L χX1bar (Y : Section1.ClassFunction L) = 0 := by
    exact h52c (h52a X1).1 Y.2 (by
      intro hEq
      exact hYneX1bar hEq.symm)
  have hYX1bar_zero :
      Section1.scalarProduct L (Y : Section1.ClassFunction L) χX1bar = 0 :=
    scalarProduct_zero_swap_pf57 hX1barY_zero
  have horthX1Y : orthogonalFinsets (R X1) (R Y) :=
    h52e Y X1 hX1Y_zero hX1Ybar_zero
  have horthYX1 : orthogonalFinsets (R Y) (R X1) :=
    h52e X1 Y hYX1_zero hYX1bar_zero
  have hX1img_orthY : orthogonalToFinset (R Y) X1img :=
    orthogonalToFinset_of_subsetSum_of_orthogonalFinsets_pf57 hX1img_subset horthX1Y
  have hXbigY_orthX1 : orthogonalToFinset (R X1) XbigY :=
    orthogonalToFinset_of_integerSpan_of_orthogonalFinsets_pf57 hXbigY_span horthXX1
  have hXbig_Yimg_zero :
      Section1.scalarProduct G Xbig Yimg = 0 := by
    have hYimg_Xbig_zero : Section1.scalarProduct G Yimg Xbig = 0 := by
      rcases hXbig_span with ⟨v, rfl⟩
      exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
        (fun r : R X => (r : Section1.ClassFunction G))
        (fun r => hYimg_orthX r.2) v
    exact scalarProduct_zero_swap_pf57 hYimg_Xbig_zero
  have hX1img_XbigY_zero :
      Section1.scalarProduct G X1img XbigY = 0 := by
    rcases hXbigY_span with ⟨v, rfl⟩
    exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
      (fun r : R X => (r : Section1.ClassFunction G))
      (fun r => hX1img_orthX r.2) v
  have hX1img_Yimg_zero :
      Section1.scalarProduct G X1img Yimg = 0 := by
    rcases integerSpan_of_subsetSum_pf57 hYimg_subset with ⟨v, rfl⟩
    exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
      (fun r : R Y => (r : Section1.ClassFunction G))
      (fun r => hX1img_orthY r.2) v
  have hXbigY_X1img_zero :
      Section1.scalarProduct G XbigY X1img = 0 := by
    rcases hX1img_span with ⟨v, rfl⟩
    exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
      (fun r : R X1 => (r : Section1.ClassFunction G))
      (fun r => hXbigY_orthX1 r.2) v
  have hYimg_Xbig_zero :
      Section1.scalarProduct G Yimg Xbig = 0 := by
    rcases hXbig_span with ⟨v, rfl⟩
    exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
      (fun r : R X => (r : Section1.ClassFunction G))
      (fun r => hYimg_orthX r.2) v
  have hYimg_X1img_zero :
      Section1.scalarProduct G Yimg X1img = 0 := by
    rcases hX1img_span with ⟨v, rfl⟩
    exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
      (fun r : R X1 => (r : Section1.ClassFunction G))
      (fun r => (orthogonalToFinset_of_subsetSum_of_orthogonalFinsets_pf57
        hYimg_subset horthYX1) r.2) v
  have hdiffXX1_memOn :
      integerSpanOn S puncturedSet (χX - χX1) := by
    simpa [χX, χX1] using diff_memOn_of_equal_degree_pf57 S X X1 (hdeg X X1)
  have hdiffXY_memOn :
      integerSpanOn S puncturedSet (χX - (Y : Section1.ClassFunction L)) := by
    simpa [χX] using diff_memOn_of_equal_degree_pf57 S X Y (hdeg X Y)
  have hcross_forward :
      Section1.scalarProduct G Xbig XbigY =
        Section1.scalarProduct L χX χX := by
    have hsrc :
        Section1.scalarProduct L (χX - χX1) (χX - (Y : Section1.ClassFunction L)) =
          Section1.scalarProduct L χX χX := by
      rw [scalarProduct_sub_left_pf57, scalarProduct_sub_right_pf57,
        scalarProduct_sub_right_pf57]
      simp [hXY_zero, hX1X_zero, hX1Y_zero]
    have htgt :
        Section1.scalarProduct G (Xbig - X1img) (XbigY - Yimg) =
          Section1.scalarProduct G Xbig XbigY := by
      rw [scalarProduct_sub_left_pf57, scalarProduct_sub_right_pf57,
        scalarProduct_sub_right_pf57]
      simp [hXbig_Yimg_zero, hX1img_XbigY_zero, hX1img_Yimg_zero]
    calc
      Section1.scalarProduct G Xbig XbigY
          = Section1.scalarProduct G (Xbig - X1img) (XbigY - Yimg) := by
              symm
              exact htgt
      _ = Section1.scalarProduct G (T (χX - χX1))
            (T (χX - (Y : Section1.ClassFunction L))) := by
              rw [hsplit_X1, hsplitY]
      _ = Section1.scalarProduct L (χX - χX1) (χX - (Y : Section1.ClassFunction L)) := by
            exact h52b.1 _ _ hdiffXX1_memOn hdiffXY_memOn
      _ = Section1.scalarProduct L χX χX := hsrc
  have hcross_backward :
      Section1.scalarProduct G XbigY Xbig =
        Section1.scalarProduct L χX χX := by
    have hsrc :
        Section1.scalarProduct L (χX - (Y : Section1.ClassFunction L)) (χX - χX1) =
          Section1.scalarProduct L χX χX := by
      rw [scalarProduct_sub_left_pf57, scalarProduct_sub_right_pf57,
        scalarProduct_sub_right_pf57]
      simp [hYX_zero, hXX1_zero, hYX1_zero]
    have htgt :
        Section1.scalarProduct G (XbigY - Yimg) (Xbig - X1img) =
          Section1.scalarProduct G XbigY Xbig := by
      rw [scalarProduct_sub_left_pf57, scalarProduct_sub_right_pf57,
        scalarProduct_sub_right_pf57]
      simp [hXbigY_X1img_zero, hYimg_Xbig_zero, hYimg_X1img_zero]
    calc
      Section1.scalarProduct G XbigY Xbig
          = Section1.scalarProduct G (XbigY - Yimg) (Xbig - X1img) := by
              symm
              exact htgt
      _ = Section1.scalarProduct G (T (χX - (Y : Section1.ClassFunction L)))
            (T (χX - χX1)) := by
              rw [hsplitY, hsplit_X1]
      _ = Section1.scalarProduct L (χX - (Y : Section1.ClassFunction L)) (χX - χX1) := by
            exact h52b.1 _ _ hdiffXY_memOn hdiffXX1_memOn
      _ = Section1.scalarProduct L χX χX := hsrc
  have hXbig_eq : Xbig = XbigY := by
    apply eq_of_self_and_cross_pf57
    · exact hXbig_self.trans hcross_forward.symm
    · exact hXbigY_self.trans hcross_forward.symm
    · exact hcross_backward.trans hcross_forward.symm
  refine ⟨Yimg, hYimg_virt, hYimg_orthX, ?_, hYimg_self⟩
  simpa [hXbig_eq] using hsplitY

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
private theorem anchored_image_of_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (h52e : hypothesis_5_2_e_statement S R)
    (hdeg : ∀ X Y : S,
      Section1.degree (X : Section1.ClassFunction L) =
        Section1.degree (Y : Section1.ClassFunction L))
    (X X1 : S)
    {Xbig X1img : Section1.ClassFunction G}
    (hX1_ne_X : (X1 : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L))
    (hX1_ne_Xbar : (X1 : Section1.ClassFunction L) ≠
      Section1.conjugateCharacter (X : Section1.ClassFunction L))
    (hXbig_span : integerSpan (R X) Xbig)
    (hX1img_span : integerSpan (R X1) X1img)
    (hX1img_subset : isSubsetSumOf (R X1) X1img)
    (hX1img_orthX : orthogonalToFinset (R X) X1img)
    (hsplit_X1 :
      T ((X : Section1.ClassFunction L) - (X1 : Section1.ClassFunction L)) =
        Xbig - X1img)
    (hXbig_self :
      Section1.scalarProduct G Xbig Xbig =
        Section1.scalarProduct L (X : Section1.ClassFunction L)
          (X : Section1.ClassFunction L))
    (hX1img_self :
      Section1.scalarProduct G X1img X1img =
        Section1.scalarProduct L (X1 : Section1.ClassFunction L)
          (X1 : Section1.ClassFunction L)) :
    ∀ Y : S,
      (Y : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L) →
        (Y : Section1.ClassFunction L) ≠
          Section1.conjugateCharacter (X : Section1.ClassFunction L) →
          ∃ Yimg : Section1.ClassFunction G,
            Theory.Character.IsVirtualCharacter Yimg ∧
              orthogonalToFinset (R X) Yimg ∧
                T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
                  Xbig - Yimg ∧
                  Section1.scalarProduct G Yimg Yimg =
                    Section1.scalarProduct L (Y : Section1.ClassFunction L)
                      (Y : Section1.ClassFunction L) := by
  classical
  let χX : Section1.ClassFunction L := X
  let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
  let χX1 : Section1.ClassFunction L := X1
  let χX1bar : Section1.ClassFunction L := Section1.conjugateCharacter χX1
  have hRX1 : signedOrthonormalFinset (R X1) := (h52d X1).1
  have hX1img_virt : Theory.Character.IsVirtualCharacter X1img :=
    isVirtualCharacter_of_subsetSum_pf57 hRX1 hX1img_subset
  have hXX1_zero :
      Section1.scalarProduct L χX χX1 = 0 := by
    exact h52c X.2 X1.2 hX1_ne_X.symm
  have hX1X_zero :
      Section1.scalarProduct L χX1 χX = 0 := scalarProduct_zero_swap_pf57 hXX1_zero
  have hX1Xbar_zero :
      Section1.scalarProduct L χX1 χXbar = 0 := by
    exact h52c X1.2 (h52a X).1 (by
      intro hEq
      exact hX1_ne_Xbar (by simpa [χX1bar] using hEq))
  have horthX1X : orthogonalFinsets (R X1) (R X) := h52e X X1 hX1X_zero hX1Xbar_zero
  intro Y hYneX hYneXbar
  by_cases hYeqX1 : Y = X1
  · subst hYeqX1
    exact ⟨X1img, hX1img_virt, hX1img_orthX, hsplit_X1, hX1img_self⟩
  · by_cases hYeqX1bar : (Y : Section1.ClassFunction L) = χX1bar
    · rcases complement_image_of_subsetSum_pf57 S T R hsetup h52a h52b h52c h52d X1
        hX1img_subset hX1img_self with
          ⟨X1barimg, hX1barimg_virt, hX1barimg_span, hX1barimg_self,
            _hX1img_X1bar_zero, _hX1bar_X1img_zero, hsplit_X1bar⟩
      have hX1barimg_orthX : orthogonalToFinset (R X) X1barimg :=
        orthogonalToFinset_of_integerSpan_of_orthogonalFinsets_pf57 hX1barimg_span horthX1X
      refine ⟨X1barimg, hX1barimg_virt, hX1barimg_orthX, ?_, ?_⟩
      · calc
          T (χX - (Y : Section1.ClassFunction L))
              = T ((χX - χX1) + (χX1 - χX1bar)) := by
                  rw [hYeqX1bar]
                  ext g
                  ring_nf
          _ = T (χX - χX1) + T (χX1 - χX1bar) := by simp
          _ = (Xbig - X1img) + (X1img - X1barimg) := by
                rw [hsplit_X1, hsplit_X1bar]
          _ = Xbig - X1barimg := by abel
      · simpa [hYeqX1bar, χX1bar] using hX1barimg_self
    · exact anchored_image_general_case_pf57 S T R hsetup h52a h52b h52c h52d h52e
        hdeg X X1 Y hX1_ne_X hX1_ne_Xbar hYneX hYneXbar hYeqX1 hYeqX1bar
        hXbig_span hX1img_span hX1img_subset hX1img_orthX hsplit_X1 hXbig_self

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
private theorem image_family_cross_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (X : S)
    (Xbig : Section1.ClassFunction G)
    (img : S → Section1.ClassFunction G)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (hdeg : ∀ Y Z : S,
      Section1.degree (Y : Section1.ClassFunction L) =
        Section1.degree (Z : Section1.ClassFunction L))
    (hXbig_self :
      Section1.scalarProduct G Xbig Xbig =
        Section1.scalarProduct L (X : Section1.ClassFunction L)
          (X : Section1.ClassFunction L))
    (himg_orthX :
      ∀ Y : S, (Y : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L) →
        Section1.scalarProduct G Xbig (img Y) = 0 ∧
          Section1.scalarProduct G (img Y) Xbig = 0)
    (himg_split :
      ∀ Y : S,
        T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
          Xbig - img Y) :
    ∀ Y Z : S, (Y : Section1.ClassFunction L) ≠ (Z : Section1.ClassFunction L) →
      Section1.scalarProduct G (img Y) (img Z) = 0 := by
  intro Y Z hYZ
  by_cases hYX : (Y : Section1.ClassFunction L) = (X : Section1.ClassFunction L)
  · have himgX : img X = Xbig := by
      have h0 : (0 : Section1.ClassFunction G) = Xbig - img X := by
        simpa using himg_split X
      ext g
      have hg := congrArg (fun f : Section1.ClassFunction G => f g) h0
      have hg' : (0 : ℂ) = Xbig g - img X g := by
        simpa using hg
      calc
        img X g = Xbig g - (Xbig g - img X g) := by ring
        _ = Xbig g - 0 := by rw [← hg']
        _ = Xbig g := by ring
    have hZneX : (Z : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L) := by
      simpa [hYX] using hYZ.symm
    have hY_eq_X : Y = X := Subtype.ext hYX
    calc
      Section1.scalarProduct G (img Y) (img Z)
          = Section1.scalarProduct G (img X) (img Z) := by rw [hY_eq_X]
      _ = Section1.scalarProduct G Xbig (img Z) := by rw [himgX]
      _ = 0 := (himg_orthX Z hZneX).1
  by_cases hZX : (Z : Section1.ClassFunction L) = (X : Section1.ClassFunction L)
  · have himgX : img X = Xbig := by
      have h0 : (0 : Section1.ClassFunction G) = Xbig - img X := by
        simpa using himg_split X
      ext g
      have hg := congrArg (fun f : Section1.ClassFunction G => f g) h0
      have hg' : (0 : ℂ) = Xbig g - img X g := by
        simpa using hg
      calc
        img X g = Xbig g - (Xbig g - img X g) := by ring
        _ = Xbig g - 0 := by rw [← hg']
        _ = Xbig g := by ring
    have hZ_eq_X : Z = X := Subtype.ext hZX
    calc
      Section1.scalarProduct G (img Y) (img Z)
          = Section1.scalarProduct G (img Y) (img X) := by rw [hZ_eq_X]
      _ = Section1.scalarProduct G (img Y) Xbig := by rw [himgX]
      _ = 0 := (himg_orthX Y hYX).2
  let χX : Section1.ClassFunction L := X
  have hXY_zero :
      Section1.scalarProduct L χX (Y : Section1.ClassFunction L) = 0 := by
    exact h52c X.2 Y.2 (by
      intro hEq
      exact hYX hEq.symm)
  have hYX_zero :
      Section1.scalarProduct L (Y : Section1.ClassFunction L) χX = 0 :=
    scalarProduct_zero_swap_pf57 hXY_zero
  have hXZ_zero :
      Section1.scalarProduct L χX (Z : Section1.ClassFunction L) = 0 := by
    exact h52c X.2 Z.2 (by
      intro hEq
      exact hZX hEq.symm)
  have hYZ_zero :
      Section1.scalarProduct L (Y : Section1.ClassFunction L)
          (Z : Section1.ClassFunction L) = 0 :=
    h52c Y.2 Z.2 hYZ
  have hX_imgZ_zero : Section1.scalarProduct G Xbig (img Z) = 0 :=
    (himg_orthX Z hZX).1
  have hYimg_X_zero : Section1.scalarProduct G (img Y) Xbig = 0 :=
    (himg_orthX Y hYX).2
  have hdiffY :
      integerSpanOn S puncturedSet (χX - (Y : Section1.ClassFunction L)) := by
    simpa [χX] using diff_memOn_of_equal_degree_pf57 S X Y (hdeg X Y)
  have hdiffZ :
      integerSpanOn S puncturedSet (χX - (Z : Section1.ClassFunction L)) := by
    simpa [χX] using diff_memOn_of_equal_degree_pf57 S X Z (hdeg X Z)
  have hsrc :
      Section1.scalarProduct L (χX - (Y : Section1.ClassFunction L))
          (χX - (Z : Section1.ClassFunction L)) =
        Section1.scalarProduct L χX χX := by
    rw [scalarProduct_sub_left_pf57, scalarProduct_sub_right_pf57,
      scalarProduct_sub_right_pf57]
    simp [hXZ_zero, hYX_zero, hYZ_zero]
  have htgt :
      Section1.scalarProduct G (Xbig - img Y) (Xbig - img Z) =
        Section1.scalarProduct G Xbig Xbig +
          Section1.scalarProduct G (img Y) (img Z) := by
    rw [scalarProduct_sub_left_pf57, scalarProduct_sub_right_pf57,
      scalarProduct_sub_right_pf57]
    simp [hX_imgZ_zero, hYimg_X_zero]
  have hiso := h52b.1 (χX - (Y : Section1.ClassFunction L))
    (χX - (Z : Section1.ClassFunction L)) hdiffY hdiffZ
  rw [himg_split Y, himg_split Z, htgt, hsrc, hXbig_self] at hiso
  have hiso' :
      Section1.scalarProduct L χX χX +
          Section1.scalarProduct G (img Y) (img Z) =
        Section1.scalarProduct L χX χX + 0 := by
    simpa [χX] using hiso
  exact add_left_cancel hiso'

private def anchoredImageSpec_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (X : S)
    (Xbig : Section1.ClassFunction G) : Prop :=
  ∀ Y : S,
    (Y : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L) →
      (Y : Section1.ClassFunction L) ≠
        Section1.conjugateCharacter (X : Section1.ClassFunction L) →
        ∃ Yimg : Section1.ClassFunction G,
          Theory.Character.IsVirtualCharacter Yimg ∧
            orthogonalToFinset (R X) Yimg ∧
              T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
                Xbig - Yimg ∧
              Section1.scalarProduct G Yimg Yimg =
                Section1.scalarProduct L (Y : Section1.ClassFunction L)
                  (Y : Section1.ClassFunction L)

private noncomputable def anchorImage_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (X : S)
    (Xbig Xbarimg : Section1.ClassFunction G)
    (hanchor : anchoredImageSpec_pf57 S T R X Xbig) :
    S → Section1.ClassFunction G := fun Y =>
  if hYX : (Y : Section1.ClassFunction L) = (X : Section1.ClassFunction L) then Xbig
  else if hYXbar : (Y : Section1.ClassFunction L) =
      Section1.conjugateCharacter (X : Section1.ClassFunction L) then Xbarimg
  else Classical.choose (hanchor Y hYX hYXbar)

private theorem anchorImage_pf57_apply_self
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (X : S)
    (Xbig Xbarimg : Section1.ClassFunction G)
    (hanchor : anchoredImageSpec_pf57 S T R X Xbig) :
    anchorImage_pf57 S T R X Xbig Xbarimg hanchor X = Xbig := by
  classical
  simp [anchorImage_pf57]

private theorem anchorImage_pf57_apply_conj
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (X : S)
    (h52a : hypothesis_5_2_a_statement S)
    (Xbig Xbarimg : Section1.ClassFunction G)
    (hanchor : anchoredImageSpec_pf57 S T R X Xbig) :
    anchorImage_pf57 S T R X Xbig Xbarimg hanchor
        ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩ = Xbarimg := by
  classical
  have hXbar_ne_X :
      (Section1.conjugateCharacter (X : Section1.ClassFunction L)) ≠
        (X : Section1.ClassFunction L) := by
    intro hEq
    exact (h52a X).2 hEq.symm
  simp [anchorImage_pf57, hXbar_ne_X]

private theorem anchorImage_pf57_virt
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (X : S)
    (Xbig Xbarimg : Section1.ClassFunction G)
    (h52d : hypothesis_5_2_d_statement S T R)
    (hXbig_subset : isSubsetSumOf (R X) Xbig)
    (hXbarimg_virt : Theory.Character.IsVirtualCharacter Xbarimg)
    (hanchor : anchoredImageSpec_pf57 S T R X Xbig) :
    ∀ Y : S, Theory.Character.IsVirtualCharacter (anchorImage_pf57 S T R X Xbig Xbarimg hanchor Y) := by
  classical
  have hRX : signedOrthonormalFinset (R X) := (h52d X).1
  intro Y
  by_cases hYX : (Y : Section1.ClassFunction L) = (X : Section1.ClassFunction L)
  · simpa [anchorImage_pf57, hYX] using
      isVirtualCharacter_of_subsetSum_pf57 hRX hXbig_subset
  · by_cases hYXbar : (Y : Section1.ClassFunction L) =
        Section1.conjugateCharacter (X : Section1.ClassFunction L)
    · have hXbar_ne_X :
          Section1.conjugateCharacter (X : Section1.ClassFunction L) ≠
            (X : Section1.ClassFunction L) := by
        intro hEq
        exact hYX (hYXbar.trans hEq)
      by_cases hself : Section1.conjugateCharacter (X : Section1.ClassFunction L) =
          (X : Section1.ClassFunction L)
      · simpa [anchorImage_pf57, hYX, hYXbar, hself] using
          isVirtualCharacter_of_subsetSum_pf57 hRX hXbig_subset
      · simpa [anchorImage_pf57, hYX, hYXbar, hXbar_ne_X, hself] using hXbarimg_virt
    · simpa [anchorImage_pf57, hYX, hYXbar] using
        (Classical.choose_spec (hanchor Y hYX hYXbar)).1

private theorem anchorImage_pf57_orthX
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (X : S)
    (Xbig Xbarimg : Section1.ClassFunction G)
    (hXbig_span : integerSpan (R X) Xbig)
    (hXbig_Xbar_zero : Section1.scalarProduct G Xbig Xbarimg = 0)
    (hXbar_Xbig_zero : Section1.scalarProduct G Xbarimg Xbig = 0)
    (hanchor : anchoredImageSpec_pf57 S T R X Xbig) :
    ∀ Y : S, (Y : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L) →
      Section1.scalarProduct G Xbig (anchorImage_pf57 S T R X Xbig Xbarimg hanchor Y) = 0 ∧
        Section1.scalarProduct G (anchorImage_pf57 S T R X Xbig Xbarimg hanchor Y) Xbig = 0 := by
  classical
  intro Y hYneX
  by_cases hYXbar : (Y : Section1.ClassFunction L) =
      Section1.conjugateCharacter (X : Section1.ClassFunction L)
  · have hXbar_ne_X :
        Section1.conjugateCharacter (X : Section1.ClassFunction L) ≠
          (X : Section1.ClassFunction L) := by
      intro hEq
      exact hYneX (hYXbar.trans hEq)
    simpa [anchorImage_pf57, hYneX, hYXbar, hXbar_ne_X] using
      ⟨hXbig_Xbar_zero, hXbar_Xbig_zero⟩
  · have hspec := Classical.choose_spec (hanchor Y hYneX hYXbar)
    have horth :
        orthogonalToFinset (R X) (anchorImage_pf57 S T R X Xbig Xbarimg hanchor Y) := by
      simpa [anchorImage_pf57, hYneX, hYXbar] using hspec.2.1
    have hYX0 :
        Section1.scalarProduct G
          (anchorImage_pf57 S T R X Xbig Xbarimg hanchor Y) Xbig = 0 := by
      rcases hXbig_span with ⟨v, rfl⟩
      exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf57
        (fun r : R X => (r : Section1.ClassFunction G))
        (fun r => horth r.2) v
    exact ⟨scalarProduct_zero_swap_pf57 hYX0, hYX0⟩

private theorem anchorImage_pf57_self
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (X : S)
    (Xbig Xbarimg : Section1.ClassFunction G)
    (hXbig_self :
      Section1.scalarProduct G Xbig Xbig =
        Section1.scalarProduct L (X : Section1.ClassFunction L)
          (X : Section1.ClassFunction L))
    (hXbarimg_self :
      Section1.scalarProduct G Xbarimg Xbarimg =
        Section1.scalarProduct L
          (Section1.conjugateCharacter (X : Section1.ClassFunction L))
          (Section1.conjugateCharacter (X : Section1.ClassFunction L)))
    (hanchor : anchoredImageSpec_pf57 S T R X Xbig) :
    ∀ Y : S,
      Section1.scalarProduct G
          (anchorImage_pf57 S T R X Xbig Xbarimg hanchor Y)
          (anchorImage_pf57 S T R X Xbig Xbarimg hanchor Y) =
        Section1.scalarProduct L (Y : Section1.ClassFunction L)
          (Y : Section1.ClassFunction L) := by
  classical
  intro Y
  by_cases hYX : (Y : Section1.ClassFunction L) = (X : Section1.ClassFunction L)
  · simpa [anchorImage_pf57, hYX] using hXbig_self
  · by_cases hYXbar : (Y : Section1.ClassFunction L) =
        Section1.conjugateCharacter (X : Section1.ClassFunction L)
    · have hXbar_ne_X :
          Section1.conjugateCharacter (X : Section1.ClassFunction L) ≠
            (X : Section1.ClassFunction L) := by
        intro hEq
        exact hYX (hYXbar.trans hEq)
      simpa [anchorImage_pf57, hYX, hYXbar, hXbar_ne_X] using hXbarimg_self
    · simpa [anchorImage_pf57, hYX, hYXbar] using
        (Classical.choose_spec (hanchor Y hYX hYXbar)).2.2.2

private theorem anchorImage_pf57_split
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (X : S)
    (Xbig Xbarimg : Section1.ClassFunction G)
    (hsplit_Xbar :
      T ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
          Xbig - Xbarimg)
    (hanchor : anchoredImageSpec_pf57 S T R X Xbig) :
    ∀ Y : S,
      T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
        anchorImage_pf57 S T R X Xbig Xbarimg hanchor X -
          anchorImage_pf57 S T R X Xbig Xbarimg hanchor Y := by
  classical
  intro Y
  by_cases hYX : (Y : Section1.ClassFunction L) = (X : Section1.ClassFunction L)
  · simp [anchorImage_pf57, hYX]
  · by_cases hYXbar : (Y : Section1.ClassFunction L) =
        Section1.conjugateCharacter (X : Section1.ClassFunction L)
    · have hXbar_ne_X :
          Section1.conjugateCharacter (X : Section1.ClassFunction L) ≠
            (X : Section1.ClassFunction L) := by
        intro hEq
        exact hYX (hYXbar.trans hEq)
      simpa [anchorImage_pf57, hYX, hYXbar, hXbar_ne_X] using hsplit_Xbar
    · simpa [anchorImage_pf57, hYX, hYXbar] using
        (Classical.choose_spec (hanchor Y hYX hYXbar)).2.2.1

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
private theorem image_family_of_anchor_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (hdeg : ∀ Y Z : S,
      Section1.degree (Y : Section1.ClassFunction L) =
        Section1.degree (Z : Section1.ClassFunction L))
    (X : S)
    (Xbig Xbarimg : Section1.ClassFunction G)
    (hXbig_span : integerSpan (R X) Xbig)
    (hXbig_subset : isSubsetSumOf (R X) Xbig)
    (hXbig_self :
      Section1.scalarProduct G Xbig Xbig =
        Section1.scalarProduct L (X : Section1.ClassFunction L)
          (X : Section1.ClassFunction L))
    (hXbarimg_virt : Theory.Character.IsVirtualCharacter Xbarimg)
    (hXbarimg_self :
      Section1.scalarProduct G Xbarimg Xbarimg =
        Section1.scalarProduct L
          (Section1.conjugateCharacter (X : Section1.ClassFunction L))
          (Section1.conjugateCharacter (X : Section1.ClassFunction L)))
    (hXbig_Xbar_zero : Section1.scalarProduct G Xbig Xbarimg = 0)
    (hXbar_Xbig_zero : Section1.scalarProduct G Xbarimg Xbig = 0)
    (hsplit_Xbar :
      T ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
          Xbig - Xbarimg)
    (hanchor : anchoredImageSpec_pf57 S T R X Xbig) :
    ∃ img : S → Section1.ClassFunction G,
      img X = Xbig ∧
      img ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩ = Xbarimg ∧
      (∀ Y : S, Theory.Character.IsVirtualCharacter (img Y)) ∧
      (∀ Y : S,
        T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
          img X - img Y) ∧
      (∀ Y : S,
        Section1.scalarProduct G (img Y) (img Y) =
          Section1.scalarProduct L (Y : Section1.ClassFunction L)
            (Y : Section1.ClassFunction L)) ∧
      (∀ Y Z : S, (Y : Section1.ClassFunction L) ≠ (Z : Section1.ClassFunction L) →
        Section1.scalarProduct G (img Y) (img Z) = 0) := by
  classical
  let img : S → Section1.ClassFunction G :=
    anchorImage_pf57 S T R X Xbig Xbarimg hanchor
  have himg_X : img X = Xbig := by
    simpa [img] using anchorImage_pf57_apply_self S T R X Xbig Xbarimg hanchor
  have himg_Xbar :
      img ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩ = Xbarimg := by
    simpa [img] using
      anchorImage_pf57_apply_conj S T R X h52a Xbig Xbarimg hanchor
  have himg_virt : ∀ Y : S, Theory.Character.IsVirtualCharacter (img Y) := by
    intro Y
    simpa [img] using
      anchorImage_pf57_virt S T R X Xbig Xbarimg h52d hXbig_subset hXbarimg_virt hanchor Y
  have himg_orthX :
      ∀ Y : S, (Y : Section1.ClassFunction L) ≠ (X : Section1.ClassFunction L) →
        Section1.scalarProduct G Xbig (img Y) = 0 ∧
          Section1.scalarProduct G (img Y) Xbig = 0 := by
    intro Y hYneX
    simpa [img] using
      anchorImage_pf57_orthX S T R X Xbig Xbarimg hXbig_span
        hXbig_Xbar_zero hXbar_Xbig_zero hanchor Y hYneX
  have himg_self :
      ∀ Y : S,
        Section1.scalarProduct G (img Y) (img Y) =
          Section1.scalarProduct L (Y : Section1.ClassFunction L)
            (Y : Section1.ClassFunction L) := by
    intro Y
    simpa [img] using
      anchorImage_pf57_self S T R X Xbig Xbarimg hXbig_self hXbarimg_self hanchor Y
  have himg_split :
      ∀ Y : S,
        T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
          img X - img Y := by
    intro Y
    simpa [img] using
      anchorImage_pf57_split S T R X Xbig Xbarimg hsplit_Xbar hanchor Y
  have himg_cross :
      ∀ Y Z : S, (Y : Section1.ClassFunction L) ≠ (Z : Section1.ClassFunction L) →
        Section1.scalarProduct G (img Y) (img Z) = 0 :=
    image_family_cross_pf57 S T X Xbig img h52b h52c hdeg
      hXbig_self himg_orthX (by
        intro Y
        simpa [himg_X] using himg_split Y)
  exact ⟨img, himg_X, himg_Xbar, himg_virt, himg_split, himg_self, himg_cross⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
private theorem agreesOnIntegerSpanOn_of_anchor_family_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (X : S)
    (img : S → Section1.ClassFunction G)
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (hdeg : ∀ Y Z : S,
      Section1.degree (Y : Section1.ClassFunction L) =
        Section1.degree (Z : Section1.ClassFunction L))
    (himg_split :
      ∀ Y : S,
        T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
          img X - img Y)
    (hTnew_basis : ∀ Y : S, Tnew (Y : Section1.ClassFunction L) = img Y) :
    agreesOnIntegerSpanOn S puncturedSet T Tnew := by
  classical
  let χX : Section1.ClassFunction L := X
  have hχXchar : Section1.IsCharacter χX := hsetup.2 X
  intro χ hχ
  rcases hχ with ⟨hχspan, hχon⟩
  rcases hχspan with ⟨v, hv⟩
  let μS : S → Section1.ClassFunction L := fun Y => (Y : Section1.ClassFunction L)
  let s : Int := ∑ Y : S, v Y
  have hdegχ : Section1.degree χ = 0 :=
    (supportedOn_puncturedSet_iff_degree_eq_zero_pf57 χ).1 hχon
  rcases degree_eq_nat_of_isCharacter_pf57 hχXchar with ⟨d, hd⟩
  have hd_ne_zero : (d : ℂ) ≠ 0 := by
    intro hd0
    have hχX_zero : χX = 0 :=
      character_eq_zero_of_degree_zero_pf57 hχXchar (hd.trans hd0)
    have hχX_bar : χX = Section1.conjugateCharacter χX := by
      calc
        χX = 0 := hχX_zero
        _ = Section1.conjugateCharacter (0 : Section1.ClassFunction L) := by
              ext g
              simp [Section1.conjugateCharacter]
        _ = Section1.conjugateCharacter χX := by simpa [hχX_zero]
    exact (h52a X).2 hχX_bar
  have hdeg_eval :
      Section1.degree χ =
        ∑ Y : S, ((v Y : ℂ) * Section1.degree (Y : Section1.ClassFunction L)) := by
    rw [hv, Section1.evalCoeff, Section1.degree_apply]
    simp [Section1.degree_apply]
  have hfactor :
      ∑ Y : S, ((v Y : ℂ) * Section1.degree (Y : Section1.ClassFunction L)) =
        (s : ℂ) * (d : ℂ) := by
    calc
      ∑ Y : S, ((v Y : ℂ) * Section1.degree (Y : Section1.ClassFunction L))
          = ∑ Y : S, ((v Y : ℂ) * (d : ℂ)) := by
              refine Finset.sum_congr rfl ?_
              intro Y _hY
              rw [hdeg Y X, hd]
      _ = (s : ℂ) * (d : ℂ) := by
            simp [s, Finset.sum_mul]
  have hsum0 : (s : ℂ) = 0 := by
    have hsum_mul : (s : ℂ) * (d : ℂ) = 0 := by
      rw [← hfactor, ← hdeg_eval, hdegχ]
    exact (mul_eq_zero.mp hsum_mul).resolve_right hd_ne_zero
  have hsource_eval :
      Section1.evalCoeff (fun Y : S => χX - (Y : Section1.ClassFunction L)) v =
        ((s : ℂ) • χX) - χ := by
    rw [hv]
    ext g
    simp [Section1.evalCoeff, s, Pi.smul_apply, mul_add, add_mul, mul_comm, mul_left_comm,
      mul_assoc, mul_sub]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro Y _hY
    ring
  have htarget_eval :
      Section1.evalCoeff (fun Y : S => T (χX - (Y : Section1.ClassFunction L))) v =
        ((s : ℂ) • img X) - Section1.evalCoeff img v := by
    have hsplit_eval :
        Section1.evalCoeff (fun Y : S => T (χX - (Y : Section1.ClassFunction L))) v =
          Section1.evalCoeff (fun Y : S => img X - img Y) v := by
      congr 1
      funext Y
      exact himg_split Y
    rw [hsplit_eval]
    ext g
    simp [Section1.evalCoeff, s, Pi.smul_apply, mul_add, add_mul, mul_comm, mul_left_comm,
      mul_assoc, sub_mul]
    rw [Finset.mul_sum]
  have himg_eval : Section1.evalCoeff img v = T χ := by
    have hEq :
        ((s : ℂ) • img X) - Section1.evalCoeff img v =
          T (((s : ℂ) • χX) - χ) := by
      calc
        ((s : ℂ) • img X) - Section1.evalCoeff img v =
            Section1.evalCoeff
              (fun Y : S => T (χX - (Y : Section1.ClassFunction L))) v := by
                symm
                exact htarget_eval
        _ = T (Section1.evalCoeff
              (fun Y : S => χX - (Y : Section1.ClassFunction L)) v) := by
                symm
                exact map_evalCoeff_pf57 T
                  (fun Y : S => χX - (Y : Section1.ClassFunction L)) v
        _ = T (((s : ℂ) • χX) - χ) := by rw [hsource_eval]
    have hEq' := hEq
    rw [hsum0, zero_smul, zero_sub] at hEq'
    have hEq'' := congrArg Neg.neg hEq'
    simpa using hEq''
  calc
    Tnew χ = Tnew (Section1.evalCoeff μS v) := by rw [hv]
    _ = Section1.evalCoeff (fun Y : S => Tnew (Y : Section1.ClassFunction L)) v := by
          exact map_evalCoeff_pf57 Tnew μS v
    _ = Section1.evalCoeff img v := by
          congr 1
          funext Y
          ext g
          exact congrArg (fun f : Section1.ClassFunction G => f g) (hTnew_basis Y)
    _ = T χ := himg_eval

private noncomputable def imageFamilyCoeff_pf57
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    (Y : S) : Section1.ClassFunction L →ₗ[ℂ] ℂ :=
  { toFun := fun φ =>
      (Section1.scalarProduct L (Y : Section1.ClassFunction L)
        (Y : Section1.ClassFunction L))⁻¹ *
          Section1.scalarProduct L φ (Y : Section1.ClassFunction L)
    map_add' := by
      intro φ ψ
      rw [Section1.scalarProduct_add_left]
      ring
    map_smul' := by
      intro z φ
      rw [Section1.scalarProduct_smul_left]
      simp [smul_eq_mul, mul_assoc, mul_comm] }

private theorem imageFamilyCoeff_basis_pf57
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L))
    (h52c : hypothesis_5_2_c_statement S)
    (hself_ne_zero :
      ∀ Y : S,
        Section1.scalarProduct L (Y : Section1.ClassFunction L)
          (Y : Section1.ClassFunction L) ≠ 0) :
    ∀ Y Z : S,
      imageFamilyCoeff_pf57 Y (Z : Section1.ClassFunction L) = if Y = Z then 1 else 0 := by
  intro Y Z
  by_cases hYZ : Y = Z
  · subst hYZ
    dsimp [imageFamilyCoeff_pf57]
    field_simp [hself_ne_zero Y]
    simp
  · dsimp [imageFamilyCoeff_pf57]
    have horth :
        Section1.scalarProduct L (Z : Section1.ClassFunction L)
          (Y : Section1.ClassFunction L) = 0 := by
      exact h52c Z.2 Y.2 (by
        intro hEq
        exact hYZ (Subtype.ext hEq.symm))
    simp [horth, hYZ]

private noncomputable def imageFamilyMap_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (img : S → Section1.ClassFunction G) :
    Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G :=
  ∑ Y : S, (imageFamilyCoeff_pf57 Y).smulRight (img Y)

private theorem imageFamilyMap_basis_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (img : S → Section1.ClassFunction G)
    (h52c : hypothesis_5_2_c_statement S)
    (hself_ne_zero :
      ∀ Y : S,
        Section1.scalarProduct L (Y : Section1.ClassFunction L)
          (Y : Section1.ClassFunction L) ≠ 0) :
    ∀ Y : S, imageFamilyMap_pf57 S img (Y : Section1.ClassFunction L) = img Y := by
  intro Y
  simpa [imageFamilyMap_pf57] using
    (by
      simp [imageFamilyCoeff_basis_pf57 S h52c hself_ne_zero] :
        (∑ Z : S, (imageFamilyCoeff_pf57 Z).smulRight (img Z))
            (Y : Section1.ClassFunction L) = img Y)

public theorem exists_extension_fields_of_image_family_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (img : S → Section1.ClassFunction G)
    (h52c : hypothesis_5_2_c_statement S)
    (hself_ne_zero :
      ∀ Y : S,
        Section1.scalarProduct L (Y : Section1.ClassFunction L)
          (Y : Section1.ClassFunction L) ≠ 0)
    (himg_virt : ∀ Y : S, Theory.Character.IsVirtualCharacter (img Y))
    (hgram :
      ∀ Y Z : S,
        Section1.scalarProduct G (img Y) (img Z) =
          Section1.scalarProduct L (Y : Section1.ClassFunction L)
            (Z : Section1.ClassFunction L))
    (hagree :
      ∀ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
        (∀ Y : S, Tnew (Y : Section1.ClassFunction L) = img Y) →
          agreesOnIntegerSpanOn S puncturedSet T Tnew) :
    ∃ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
      isCFLinearIsometryOnSpan S Tnew ∧
        mapsIntegerSpanToVirtualCharacters S Tnew ∧
          agreesOnIntegerSpanOn S puncturedSet T Tnew := by
  classical
  let Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G :=
    imageFamilyMap_pf57 S img
  have hTnew_basis : ∀ Y : S, Tnew (Y : Section1.ClassFunction L) = img Y := by
    intro Y
    simpa [Tnew] using imageFamilyMap_basis_pf57 S img h52c hself_ne_zero Y
  have hIso :
      isCFLinearIsometryOnSpan S Tnew := by
    intro φ ψ hφ hψ
    rcases hφ with ⟨v, rfl⟩
    rcases hψ with ⟨w, rfl⟩
    let μS : S → Section1.ClassFunction L := fun Y => (Y : Section1.ClassFunction L)
    rw [map_evalCoeff_pf57 Tnew μS v, map_evalCoeff_pf57 Tnew μS w]
    simpa [μS, hTnew_basis] using
      scalarProduct_evalCoeff_eq_of_gram_eq_pf57 μS img hgram v w
  have hVirt :
      mapsIntegerSpanToVirtualCharacters S Tnew := by
    intro χ hχ
    rcases hχ with ⟨v, rfl⟩
    let μS : S → Section1.ClassFunction L := fun Y => (Y : Section1.ClassFunction L)
    rw [map_evalCoeff_pf57 Tnew μS v]
    simpa [μS, hTnew_basis] using
      isVirtualCharacter_evalCoeff_pf57 img himg_virt v
  exact ⟨Tnew, hIso, hVirt, hagree Tnew hTnew_basis⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
private theorem coherent_triple_of_image_family_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (X : S)
    (img : S → Section1.ClassFunction G)
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52c : hypothesis_5_2_c_statement S)
    (hdeg : ∀ Y Z : S,
      Section1.degree (Y : Section1.ClassFunction L) =
        Section1.degree (Z : Section1.ClassFunction L))
    (himg_virt : ∀ Y : S, Theory.Character.IsVirtualCharacter (img Y))
    (himg_split :
      ∀ Y : S,
        T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
          img X - img Y)
    (himg_self :
      ∀ Y : S,
        Section1.scalarProduct G (img Y) (img Y) =
          Section1.scalarProduct L (Y : Section1.ClassFunction L)
            (Y : Section1.ClassFunction L))
    (himg_cross :
      ∀ Y Z : S, (Y : Section1.ClassFunction L) ≠ (Z : Section1.ClassFunction L) →
        Section1.scalarProduct G (img Y) (img Z) = 0) :
    ∃ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
      isCFLinearIsometryOnSpan S Tnew ∧
        mapsIntegerSpanToVirtualCharacters S Tnew ∧
          agreesOnIntegerSpanOn S puncturedSet T Tnew := by
  classical
  have hself_ne_zero :
      ∀ Y : S,
        Section1.scalarProduct L (Y : Section1.ClassFunction L)
          (Y : Section1.ClassFunction L) ≠ 0 := by
    intro Y h0
    have hYchar : Section1.IsCharacter (Y : Section1.ClassFunction L) := hsetup.2 Y
    have hYself :
        Section1.scalarProduct L (Y : Section1.ClassFunction L)
          (Y : Section1.ClassFunction L) =
            (cfNormSq (Y : Section1.ClassFunction L) : ℂ) :=
      scalarProduct_self_eq_cfNormSq_of_character_pf57 hYchar
    have hcf0 : cfNormSq (Y : Section1.ClassFunction L) = 0 := by
      have hcast : ((cfNormSq (Y : Section1.ClassFunction L) : ℝ) : ℂ) = 0 := by
        rw [← hYself, h0]
      exact_mod_cast hcast
    have hYzero : (Y : Section1.ClassFunction L) = 0 := cfNormSq_eq_zero_pf57 hcf0
    have hYbar :
        (Y : Section1.ClassFunction L) =
          Section1.conjugateCharacter (Y : Section1.ClassFunction L) := by
      calc
        (Y : Section1.ClassFunction L) = 0 := hYzero
        _ = Section1.conjugateCharacter (0 : Section1.ClassFunction L) := by
              ext g
              simp [Section1.conjugateCharacter]
        _ = Section1.conjugateCharacter (Y : Section1.ClassFunction L) := by
              simpa [hYzero]
    exact (h52a Y).2 hYbar
  let Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G :=
    imageFamilyMap_pf57 S img
  have hTnew_basis : ∀ Y : S, Tnew (Y : Section1.ClassFunction L) = img Y := by
    intro Y
    simpa [Tnew] using imageFamilyMap_basis_pf57 S img h52c hself_ne_zero Y
  have hgramS :
      ∀ Y Z : S,
        Section1.scalarProduct G (img Y) (img Z) =
          Section1.scalarProduct L (Y : Section1.ClassFunction L)
            (Z : Section1.ClassFunction L) := by
    intro Y Z
    by_cases hYZ : (Y : Section1.ClassFunction L) = (Z : Section1.ClassFunction L)
    · have hYZ' : Y = Z := Subtype.ext hYZ
      subst hYZ'
      simpa using himg_self Y
    · rw [himg_cross Y Z hYZ]
      exact (h52c Y.2 Z.2 hYZ).symm
  have hIso :
      isCFLinearIsometryOnSpan S Tnew := by
    intro φ ψ hφ hψ
    rcases hφ with ⟨v, rfl⟩
    rcases hψ with ⟨w, rfl⟩
    let μS : S → Section1.ClassFunction L := fun Y => (Y : Section1.ClassFunction L)
    rw [map_evalCoeff_pf57 Tnew μS v, map_evalCoeff_pf57 Tnew μS w]
    simpa [μS, hTnew_basis] using
      scalarProduct_evalCoeff_eq_of_gram_eq_pf57 μS img hgramS v w
  have hVirt :
      mapsIntegerSpanToVirtualCharacters S Tnew := by
    intro χ hχ
    rcases hχ with ⟨v, rfl⟩
    let μS : S → Section1.ClassFunction L := fun Y => (Y : Section1.ClassFunction L)
    rw [map_evalCoeff_pf57 Tnew μS v]
    simpa [μS, hTnew_basis] using
      isVirtualCharacter_evalCoeff_pf57 img himg_virt v
  have hAgree :
      agreesOnIntegerSpanOn S puncturedSet T Tnew :=
    agreesOnIntegerSpanOn_of_anchor_family_pf57
      S T Tnew X img hsetup h52a hdeg himg_split hTnew_basis
  exact ⟨Tnew, hIso, hVirt, hAgree⟩

/-- If a finite source family has an image family with the same Gram matrix and
whose differences agree with `T` from a fixed anchor, then it supplies the
extension witnessing coherence. This is the reusable interface to the PF
`(1.4)` output used later in Section 12. -/
public theorem coherent_triple_of_image_family
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (X : S)
    (img : S → Section1.ClassFunction G)
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52c : hypothesis_5_2_c_statement S)
    (hdeg : ∀ Y Z : S,
      Section1.degree (Y : Section1.ClassFunction L) =
        Section1.degree (Z : Section1.ClassFunction L))
    (himg_virt : ∀ Y : S, Theory.Character.IsVirtualCharacter (img Y))
    (himg_split :
      ∀ Y : S,
        T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
          img X - img Y)
    (himg_self :
      ∀ Y : S,
        Section1.scalarProduct G (img Y) (img Y) =
          Section1.scalarProduct L (Y : Section1.ClassFunction L)
            (Y : Section1.ClassFunction L))
    (himg_cross :
      ∀ Y Z : S, (Y : Section1.ClassFunction L) ≠ (Z : Section1.ClassFunction L) →
        Section1.scalarProduct G (img Y) (img Z) = 0) :
    ∃ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
      isCFLinearIsometryOnSpan S Tnew ∧
        mapsIntegerSpanToVirtualCharacters S Tnew ∧
          agreesOnIntegerSpanOn S puncturedSet T Tnew :=
  coherent_triple_of_image_family_pf57
    S T X img hsetup h52a h52c hdeg himg_virt himg_split himg_self himg_cross

set_option maxHeartbeats 1000000 in
private theorem theorem_5_7_pair_case_pf57
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hsetup : hypothesis_5_2_setup_statement S)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (hcard2 : S.card = 2) :
    definition_5_1_statement puncturedSet S T := by
  classical
  obtain ⟨X0, hX0mem⟩ := hsetup.1
  let X : S := ⟨X0, hX0mem⟩
  let χX : Section1.ClassFunction L := X
  let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
  let Xbar : S := ⟨χXbar, (h52a X).1⟩
  have hS_eq_pair :
      S = ({χX, χXbar} : Finset (Section1.ClassFunction L)) := by
    simpa [χX, χXbar] using
      finset_eq_pair_of_card_two_of_conj_stable_pf57 S h52a X hcard2
  have hχXchar : Section1.IsCharacter χX := hsetup.2 X
  have hX_ne_Xbar : X ≠ Xbar := by
    intro hEq
    apply (h52a X).2
    exact congrArg (fun Y : S => (Y : Section1.ClassFunction L)) hEq
  have hXbar_ne_X : Xbar ≠ X := fun hEq => hX_ne_Xbar hEq.symm
  have hY_cases : ∀ Y : S, Y = X ∨ Y = Xbar := by
    intro Y
    have hmem :
        (Y : Section1.ClassFunction L) = χX ∨
          (Y : Section1.ClassFunction L) = χXbar := by
      simpa [hS_eq_pair, Finset.mem_insert, Finset.mem_singleton] using Y.2
    rcases hmem with hY | hY
    · left
      exact Subtype.ext hY
    · right
      exact Subtype.ext hY
  rcases pair_case_image_split_pf57 S T R hsetup h52a h52b h52c h52d X with
    ⟨Xbig, Xbarimg, hXbig_virt, hXbarimg_virt, hXbig_self, hXbarimg_self,
      hXbig_Xbar_zero, hXbar_Xbig_zero, hdiff_img⟩
  let img : S → Section1.ClassFunction G := fun Y => if Y = X then Xbig else Xbarimg
  have hdeg :
      ∀ Y Z : S,
        Section1.degree (Y : Section1.ClassFunction L) =
          Section1.degree (Z : Section1.ClassFunction L) := by
    intro Y Z
    rcases hY_cases Y with rfl | rfl <;> rcases hY_cases Z with rfl | rfl
    · rfl
    · simpa [Xbar, χXbar] using
        (degree_conjugateCharacter_eq_of_isCharacter_pf57 hχXchar).symm
    · simpa [Xbar, χXbar] using
        degree_conjugateCharacter_eq_of_isCharacter_pf57 hχXchar
    · rfl
  have himg_virt : ∀ Y : S, Theory.Character.IsVirtualCharacter (img Y) := by
    intro Y
    rcases hY_cases Y with rfl | rfl
    · simpa [img] using hXbig_virt
    · simpa [img, Xbar, hXbar_ne_X] using hXbarimg_virt
  have himg_split :
      ∀ Y : S,
        T ((X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L)) =
          img X - img Y := by
    intro Y
    rcases hY_cases Y with rfl | rfl
    · simp [img]
    · simpa [img, Xbar, hXbar_ne_X] using hdiff_img.symm
  have himg_self :
      ∀ Y : S,
        Section1.scalarProduct G (img Y) (img Y) =
          Section1.scalarProduct L (Y : Section1.ClassFunction L)
            (Y : Section1.ClassFunction L) := by
    intro Y
    rcases hY_cases Y with rfl | rfl
    · simpa [img] using hXbig_self
    · simpa [img, Xbar, hXbar_ne_X] using hXbarimg_self
  have himg_cross :
      ∀ Y Z : S, (Y : Section1.ClassFunction L) ≠ (Z : Section1.ClassFunction L) →
        Section1.scalarProduct G (img Y) (img Z) = 0 := by
    intro Y Z hYZ
    rcases hY_cases Y with rfl | rfl <;> rcases hY_cases Z with rfl | rfl
    · exact (hYZ rfl).elim
    · simpa [img, Xbar, hXbar_ne_X] using hXbig_Xbar_zero
    · simpa [img, Xbar, hXbar_ne_X] using hXbar_Xbig_zero
    · exact (hYZ rfl).elim
  rcases coherent_triple_of_image_family_pf57
      S T X img hsetup h52a h52c hdeg
      himg_virt himg_split himg_self himg_cross with
    ⟨Tnew, hIso, hVirt, hAgree⟩
  have hdiff_span : integerSpan S (χX - χXbar) := by
    exact integerSpan_sub_pf57
      (integerSpan_of_mem_pf57 S X.2)
      (integerSpan_of_mem_pf57 S Xbar.2)
  have hdiff_on : Section1.supportedOn (χX - χXbar) puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf57 _).2
    calc
      Section1.degree (χX - χXbar) =
          Section1.degree χX - Section1.degree χXbar := by
            rfl
      _ = 0 := by
            rw [degree_conjugateCharacter_eq_of_isCharacter_pf57 hχXchar]
            simp
  have hdiff_ne_zero : χX - χXbar ≠ 0 := by
    intro hzero
    exact hX_ne_Xbar (Subtype.ext (sub_eq_zero.mp hzero))
  have hS_virtual : sourceVirtualCharacters S := by
    intro χ hχ
    exact isVirtualCharacter_of_isCharacter (hsetup.2 ⟨χ, hχ⟩)
  exact ⟨hS_virtual, ⟨χX - χXbar, ⟨hdiff_span, hdiff_on⟩, hdiff_ne_zero⟩,
    Tnew, hIso, hVirt, hAgree⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.tacticAnalysis false in
set_option linter.tacticAnalysis.introMerge false in
public theorem theorem_5_7
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_5_7_statement S T := by
  intro R hsetup h52a h52b h52c h52d h52e hdeg
  by_cases hcard2 : S.card = 2
  · exact theorem_5_7_pair_case_pf57 S T R hsetup h52a h52b h52c h52d hcard2
  · rcases theorem_5_7_general_source_data_pf57 S hsetup h52a h52c hcard2 hdeg with
      ⟨X, X1, hX1_ne_X, hX1_ne_Xbar, hdiff_X_X1, hdiff_X_Xbar,
        hX_X1_zero, hXbar_X1_zero⟩
    rcases theorem_5_7_projection_data_pf57 S T R hsetup h52a h52b h52c h52d h52e
        X X1 hdiff_X_X1 hdiff_X_Xbar hX_X1_zero hXbar_X1_zero with
      ⟨Xbig, Y, hXbig_span, hY_orth, hTdiff_eq, hXbig_ge, h54eq⟩
    rcases diff_image_split_of_equal_degree_pf57 S T R hsetup h52a h52b h52c h52d
        h52e hdeg X X1 hX1_ne_X hX1_ne_Xbar with
      ⟨Xbig₀, Yimg₀, hXbig₀_span, hYimg₀_span, hXbig₀_subset,
        hYimg₀_subset, _hXbig₀_orthY, hYimg₀_orthX, hsplit₀,
        _hXbig₀_self, hYimg₀_self⟩
    have hRX : signedOrthonormalFinset (R X) := (h52d X).1
    have hXbig_eq_Xbig₀ : Xbig = Xbig₀ := by
      apply projection_component_unique_pf57 hRX hXbig_span hXbig₀_span hY_orth hYimg₀_orthX
      calc
        Xbig - Y = T ((X : Section1.ClassFunction L) - (X1 : Section1.ClassFunction L)) :=
          hTdiff_eq.symm
        _ = Xbig₀ - Yimg₀ := hsplit₀
    have hY_eq_Yimg₀ : Y = Yimg₀ := by
      ext g
      have hEq := congrArg (fun f : Section1.ClassFunction G => f g)
        (by
          calc
            Xbig - Y = T ((X : Section1.ClassFunction L) - (X1 : Section1.ClassFunction L)) :=
              hTdiff_eq.symm
            _ = Xbig₀ - Yimg₀ := hsplit₀)
      have hEq' : Xbig g + -Y g = Xbig g + -Yimg₀ g := by
        simpa [sub_eq_add_neg, hXbig_eq_Xbig₀] using hEq
      have hNeg : -Y g = -Yimg₀ g := add_left_cancel hEq'
      simpa using hNeg
    have hY_cf :
        cfNormSq Y = cfNormSq (X1 : Section1.ClassFunction L) := by
      unfold cfNormSq
      rw [hY_eq_Yimg₀]
      exact congrArg Complex.re hYimg₀_self
    have hY_ge : cfNormSq Y ≥ cfNormSq (X1 : Section1.ClassFunction L) := by
      rw [hY_cf]
    rcases h54eq hY_ge with ⟨hXbig_cf, hY_cf', hXbig_subset⟩
    let χX : Section1.ClassFunction L := X
    let χXbar : Section1.ClassFunction L := Section1.conjugateCharacter χX
    have hχXchar : Section1.IsCharacter χX := hsetup.2 X
    have hXbig_self :
        Section1.scalarProduct G Xbig Xbig =
          Section1.scalarProduct L χX χX := by
      calc
        Section1.scalarProduct G Xbig Xbig = (cfNormSq Xbig : ℂ) := by
          exact scalarProduct_self_eq_cfNormSq_of_subsetSum_pf57 hRX hXbig_subset
        _ = (cfNormSq χX : ℂ) := by rw [hXbig_cf]
        _ = Section1.scalarProduct L χX χX := by
          symm
          exact scalarProduct_self_eq_cfNormSq_of_character_pf57 hχXchar
    rcases complement_image_of_subsetSum_pf57 S T R hsetup h52a h52b h52c h52d
        X hXbig_subset hXbig_self with
      ⟨Xbarimg, hXbarimg_virt, _hXbarimg_span, hXbarimg_self,
        hXbig_Xbar_zero, hXbar_Xbig_zero, hsplit_Xbar⟩
    have hanchor := anchored_image_of_pf57 S T R hsetup h52a h52b h52c h52d h52e
      hdeg X X1 hX1_ne_X hX1_ne_Xbar hXbig_span hYimg₀_span
      hYimg₀_subset hYimg₀_orthX (by simpa [hXbig_eq_Xbig₀] using hsplit₀)
      hXbig_self hYimg₀_self
    rcases image_family_of_anchor_pf57 S T R hsetup h52a h52b h52c h52d hdeg
        X Xbig Xbarimg hXbig_span hXbig_subset hXbig_self hXbarimg_virt hXbarimg_self
        hXbig_Xbar_zero hXbar_Xbig_zero hsplit_Xbar.symm hanchor with
      ⟨img, _himg_X, _himg_Xbar, himg_virt, himg_split, himg_self, himg_cross⟩
    rcases coherent_triple_of_image_family_pf57 S T X img hsetup h52a h52c hdeg
        himg_virt himg_split himg_self himg_cross with
      ⟨Tnew, hIso, hVirt, hAgree⟩
    have hXbar_mem : χXbar ∈ S := (h52a X).1
    have hdiff_span : integerSpan S (χX - χXbar) := by
      exact integerSpan_sub_pf57
        (integerSpan_of_mem_pf57 S X.2)
        (integerSpan_of_mem_pf57 S hXbar_mem)
    have hdiff_on : Section1.supportedOn (χX - χXbar) puncturedSet := by
      apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf57 _).2
      calc
        Section1.degree (χX - χXbar) =
            Section1.degree χX - Section1.degree χXbar := by
              rfl
        _ = 0 := by
              rw [degree_conjugateCharacter_eq_of_isCharacter_pf57 hχXchar]
              simp [χXbar]
    have hdiff_ne_zero : χX - χXbar ≠ 0 := by
      intro hzero
      exact (h52a X).2 (by
        simpa [χXbar] using sub_eq_zero.mp hzero)
    have hS_virtual : sourceVirtualCharacters S := by
      intro χ hχ
      exact isVirtualCharacter_of_isCharacter (hsetup.2 ⟨χ, hχ⟩)
    exact ⟨hS_virtual, ⟨χX - χXbar, ⟨hdiff_span, hdiff_on⟩, hdiff_ne_zero⟩,
      Tnew, hIso, hVirt, hAgree⟩

private theorem evalCoeff_disjoint_union_pf57
    {L : Type u} [Group L]
    [DecidableEq (Section1.ClassFunction L)]
    (S1 S2 : Finset (Section1.ClassFunction L))
    (hdisjoint : Disjoint S1 S2)
    (v : Section1.CoeffVector
      {X : Section1.ClassFunction L // X ∈ (S1 ∪ S2)}) :
    Section1.evalCoeff
        (fun X : {X : Section1.ClassFunction L // X ∈ (S1 ∪ S2)} =>
          (X : Section1.ClassFunction L)) v =
      Section1.evalCoeff
          (fun X : S1 => (X : Section1.ClassFunction L))
          (fun X => v ⟨X, Finset.mem_union_left S2 X.2⟩) +
        Section1.evalCoeff
          (fun X : S2 => (X : Section1.ClassFunction L))
          (fun X => v ⟨X, Finset.mem_union_right S1 X.2⟩) := by
  ext g
  let w : Section1.ClassFunction L → ℤ := fun X =>
    if hX : X ∈ S1 ∪ S2 then v ⟨X, hX⟩ else 0
  have hsum := Finset.sum_union hdisjoint
      (f := fun X : Section1.ClassFunction L => (w X : ℂ) * X g)
  have hleft :
      Section1.evalCoeff
          (fun X : {X : Section1.ClassFunction L // X ∈ (S1 ∪ S2)} =>
            (X : Section1.ClassFunction L)) v g =
        ∑ X ∈ S1 ∪ S2, (w X : ℂ) * X g := by
    rw [← (S1 ∪ S2).sum_attach, Finset.attach_eq_univ]
    simp only [Section1.evalCoeff, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro X _hX
    dsimp [w]
    rw [if_pos X.2]
  have hright1 :
      Section1.evalCoeff
          (fun X : S1 => (X : Section1.ClassFunction L))
          (fun X => v ⟨X, Finset.mem_union_left S2 X.2⟩) g =
        ∑ X ∈ S1, (w X : ℂ) * X g := by
    rw [← S1.sum_attach, Finset.attach_eq_univ]
    simp only [Section1.evalCoeff, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro X _hX
    simp [w, X.2]
  have hright2 :
      Section1.evalCoeff
          (fun X : S2 => (X : Section1.ClassFunction L))
          (fun X => v ⟨X, Finset.mem_union_right S1 X.2⟩) g =
        ∑ X ∈ S2, (w X : ℂ) * X g := by
    rw [← S2.sum_attach, Finset.attach_eq_univ]
    simp only [Section1.evalCoeff, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro X _hX
    simp [w, X.2]
  exact hleft.trans (hsum.trans (congrArg₂ (· + ·) hright1.symm hright2.symm))

private theorem degree_eq_int_of_integerSpan_characters_pf57
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L))
    (hchar : ∀ X : S, Section1.IsCharacter (X : Section1.ClassFunction L))
    {φ : Section1.ClassFunction L}
    (hφ : integerSpan S φ) :
    ∃ z : ℤ, Section1.degree φ = (z : ℂ) := by
  rcases hφ with ⟨v, rfl⟩
  choose d hd using fun X : S => degree_eq_nat_of_isCharacter_pf57 (hchar X)
  refine ⟨∑ X : S, v X * (d X : ℤ), ?_⟩
  rw [Section1.degree_apply]
  simp only [Section1.evalCoeff, Finset.sum_apply, Pi.smul_apply]
  simp_rw [← Section1.degree_apply, hd]
  norm_num [Int.cast_sum, Int.cast_mul]


public theorem bridgeCoherentExtensions
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S S1 S2 : Finset (Section1.ClassFunction L))
    (T T1 T2 :
      Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h52 : hypothesis_5_2_statement S T)
    (hS1sub : S1 ⊆ S)
    (hS2sub : S2 ⊆ S)
    (hS1closed : ∀ χ : Section1.ClassFunction L, χ ∈ S1 →
      Section1.conjugateCharacter χ ∈ S1)
    (hS2closed : ∀ χ : Section1.ClassFunction L, χ ∈ S2 →
      Section1.conjugateCharacter χ ∈ S2)
    (hdisjoint : Disjoint S1 S2)
    (hExt1 : isCFLinearIsometryOnSpan S1 T1 ∧
      mapsIntegerSpanToVirtualCharacters S1 T1 ∧
      agreesOnIntegerSpanOn S1 puncturedSet T T1)
    (hExt2 : isCFLinearIsometryOnSpan S2 T2 ∧
      mapsIntegerSpanToVirtualCharacters S2 T2 ∧
      agreesOnIntegerSpanOn S2 puncturedSet T T2)
    (horth : orthogonalFinsets (S1.image T1) (S2.image T2))
    {χ φ : Section1.ClassFunction L}
    (hχ : χ ∈ S1)
    (hφ : integerSpan S2 φ)
    (hanchorOn : Section1.supportedOn (χ - φ) puncturedSet)
    (hanchor : T (χ - φ) = T1 χ - T2 φ) :
    definition_5_1_statement puncturedSet (S1 ∪ S2) T := by
  classical
  let U : Finset (Section1.ClassFunction L) := S1 ∪ S2
  have hUsub : U ⊆ S := by
    intro ξ hξ
    rcases Finset.mem_union.mp hξ with hξ | hξ
    · exact hS1sub hξ
    · exact hS2sub hξ
  have hUclosed : ∀ ξ : Section1.ClassFunction L, ξ ∈ U →
      Section1.conjugateCharacter ξ ∈ U := by
    intro ξ hξ
    rcases Finset.mem_union.mp hξ with hξ | hξ
    · exact Finset.mem_union.mpr (Or.inl (hS1closed ξ hξ))
    · exact Finset.mem_union.mpr (Or.inr (hS2closed ξ hξ))
  have hχU : χ ∈ U := Finset.mem_union.mpr (Or.inl hχ)
  have h52U : hypothesis_5_2_statement U T :=
    hypothesis_5_2_statement_subset hUsub ⟨χ, hχU⟩ hUclosed h52
  rcases h52U with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have h52UFull : hypothesis_5_2_statement U T :=
    ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  let img : U → Section1.ClassFunction G := fun X =>
    if hX : (X : Section1.ClassFunction L) ∈ S1 then
      T1 (X : Section1.ClassFunction L)
    else
      T2 (X : Section1.ClassFunction L)
  have himgVirt : ∀ X : U, Theory.Character.IsVirtualCharacter (img X) := by
    intro X
    by_cases hX : (X : Section1.ClassFunction L) ∈ S1
    · simp only [img, dif_pos hX]
      exact hExt1.2.1 _ (integerSpan_of_mem S1 hX)
    · have hX2 : (X : Section1.ClassFunction L) ∈ S2 := by
        rcases Finset.mem_union.mp X.2 with hX1 | hX2
        · exact (hX hX1).elim
        · exact hX2
      simp only [img, dif_neg hX]
      exact hExt2.2.1 _ (integerSpan_of_mem S2 hX2)
  have himgGram : ∀ X Y : U,
      Section1.scalarProduct G (img X) (img Y) =
        Section1.scalarProduct L
          (X : Section1.ClassFunction L) (Y : Section1.ClassFunction L) := by
    intro X Y
    by_cases hX : (X : Section1.ClassFunction L) ∈ S1
    · by_cases hY : (Y : Section1.ClassFunction L) ∈ S1
      · simpa only [img, dif_pos hX, dif_pos hY] using
          hExt1.1 _ _ (integerSpan_of_mem S1 hX) (integerSpan_of_mem S1 hY)
      · have hY2 : (Y : Section1.ClassFunction L) ∈ S2 := by
          rcases Finset.mem_union.mp Y.2 with hY1 | hY2
          · exact (hY hY1).elim
          · exact hY2
        have hXY : (X : Section1.ClassFunction L) ≠ Y := by
          intro hEq
          exact Finset.disjoint_left.mp hdisjoint hX (hEq ▸ hY2)
        have hsource : Section1.scalarProduct L
            (X : Section1.ClassFunction L) (Y : Section1.ClassFunction L) = 0 :=
          h52c X.2 Y.2 hXY
        have htarget : Section1.scalarProduct G
            (T1 (X : Section1.ClassFunction L))
            (T2 (Y : Section1.ClassFunction L)) = 0 :=
          horth (Finset.mem_image.mpr ⟨X, hX, rfl⟩)
            (Finset.mem_image.mpr ⟨Y, hY2, rfl⟩)
        simp only [img, dif_pos hX, dif_neg hY, htarget, hsource]
    · have hX2 : (X : Section1.ClassFunction L) ∈ S2 := by
        rcases Finset.mem_union.mp X.2 with hX1 | hX2
        · exact (hX hX1).elim
        · exact hX2
      by_cases hY : (Y : Section1.ClassFunction L) ∈ S1
      · have hXY : (X : Section1.ClassFunction L) ≠ Y := by
          intro hEq
          exact Finset.disjoint_left.mp hdisjoint hY (hEq.symm ▸ hX2)
        have hsource : Section1.scalarProduct L
            (X : Section1.ClassFunction L) (Y : Section1.ClassFunction L) = 0 :=
          h52c X.2 Y.2 hXY
        have hforward : Section1.scalarProduct G
            (T1 (Y : Section1.ClassFunction L))
            (T2 (X : Section1.ClassFunction L)) = 0 :=
          horth (Finset.mem_image.mpr ⟨Y, hY, rfl⟩)
            (Finset.mem_image.mpr ⟨X, hX2, rfl⟩)
        have htarget : Section1.scalarProduct G
            (T2 (X : Section1.ClassFunction L))
            (T1 (Y : Section1.ClassFunction L)) = 0 := by
          simpa [Section1.scalarProduct_star_swap] using congrArg star hforward
        simp only [img, dif_neg hX, dif_pos hY, htarget, hsource]
      · have hY2 : (Y : Section1.ClassFunction L) ∈ S2 := by
          rcases Finset.mem_union.mp Y.2 with hY1 | hY2
          · exact (hY hY1).elim
          · exact hY2
        simpa only [img, dif_neg hX, dif_neg hY] using
          hExt2.1 _ _ (integerSpan_of_mem S2 hX2) (integerSpan_of_mem S2 hY2)
  have hselfNe : ∀ X : U,
      Section1.scalarProduct L (X : Section1.ClassFunction L) X ≠ 0 := by
    intro X hzero
    have hself : Section1.scalarProduct L
        (X : Section1.ClassFunction L) X =
          (cfNormSq (X : Section1.ClassFunction L) : ℂ) :=
      scalarProduct_self_eq_cfNormSq_of_character (hsetup.2 X)
    have hcfC : (cfNormSq (X : Section1.ClassFunction L) : ℂ) = 0 := by
      simpa [hself] using hzero
    have hcf : cfNormSq (X : Section1.ClassFunction L) = 0 := by
      exact_mod_cast hcfC
    have hXzero : (X : Section1.ClassFunction L) = 0 := cfNormSq_eq_zero hcf
    apply (h52a X).2
    ext g
    simp [hXzero, Section1.conjugateCharacter]
  have hagree : ∀ Tnew : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
      (∀ X : U, Tnew (X : Section1.ClassFunction L) = img X) →
        agreesOnIntegerSpanOn U puncturedSet T Tnew := by
    intro Tnew hTnew η hη
    rcases hη with ⟨⟨v, hv⟩, hηOn⟩
    let v1 : Section1.CoeffVector S1 := fun X =>
      v ⟨X, Finset.mem_union_left S2 X.2⟩
    let v2 : Section1.CoeffVector S2 := fun X =>
      v ⟨X, Finset.mem_union_right S1 X.2⟩
    let η1 : Section1.ClassFunction L :=
      Section1.evalCoeff (fun X : S1 => (X : Section1.ClassFunction L)) v1
    let η2 : Section1.ClassFunction L :=
      Section1.evalCoeff (fun X : S2 => (X : Section1.ClassFunction L)) v2
    have hηSplit : η = η1 + η2 := by
      rw [hv]
      exact evalCoeff_disjoint_union_pf57 S1 S2 hdisjoint v
    have hη1Span : integerSpan S1 η1 := ⟨v1, rfl⟩
    have hη2Span : integerSpan S2 η2 := ⟨v2, rfl⟩
    rcases degree_eq_int_of_integerSpan_characters_pf57 S1
        (fun X => hsetup.2 ⟨X, Finset.mem_union_left S2 X.2⟩) hη1Span with
      ⟨a, hη1Degree⟩
    rcases degree_eq_nat_of_isCharacter_pf57
        (hsetup.2 ⟨χ, hχU⟩) with ⟨c, hχDegree⟩
    have hc : (c : ℂ) ≠ 0 := by
      intro hc0
      have hχDegreeZero : Section1.degree χ = 0 := hχDegree.trans hc0
      have hχzero : χ = 0 :=
        character_eq_zero_of_degree_zero_pf57 (hsetup.2 ⟨χ, hχU⟩) hχDegreeZero
      apply (h52a ⟨χ, hχU⟩).2
      ext g
      simp [hχzero, Section1.conjugateCharacter]
    have hηDegree : Section1.degree η = 0 :=
      (supportedOn_puncturedSet_iff_degree_eq_zero_pf57 η).1 hηOn
    have hη2Degree : Section1.degree η2 = -(a : ℂ) := by
      rw [hηSplit] at hηDegree
      change Section1.degree η1 + Section1.degree η2 = 0 at hηDegree
      rw [hη1Degree] at hηDegree
      linear_combination hηDegree
    have hanchorDegree : Section1.degree χ = Section1.degree φ := by
      have hzero :=
        (supportedOn_puncturedSet_iff_degree_eq_zero_pf57 (χ - φ)).1 hanchorOn
      change Section1.degree χ - Section1.degree φ = 0 at hzero
      exact sub_eq_zero.mp hzero
    let η1zero : Section1.ClassFunction L :=
      (c : ℂ) • η1 - (a : ℂ) • χ
    let η2zero : Section1.ClassFunction L :=
      (c : ℂ) • η2 + (a : ℂ) • φ
    have hη1zeroSpan : integerSpan S1 η1zero := by
      dsimp [η1zero]
      exact integerSpan_sub
        (by simpa using integerSpan_zsmul (S := S1) (c : ℤ) hη1Span)
        (integerSpan_zsmul (S := S1) a (integerSpan_of_mem S1 hχ))
    have hη2zeroSpan : integerSpan S2 η2zero := by
      dsimp [η2zero]
      exact integerSpan_add
        (by simpa using integerSpan_zsmul (S := S2) (c : ℤ) hη2Span)
        (integerSpan_zsmul (S := S2) a hφ)
    have hη1zeroOn : Section1.supportedOn η1zero puncturedSet := by
      apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf57 η1zero).2
      change (c : ℂ) * Section1.degree η1 - (a : ℂ) * Section1.degree χ = 0
      rw [hη1Degree, hχDegree]
      ring
    have hη2zeroOn : Section1.supportedOn η2zero puncturedSet := by
      apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf57 η2zero).2
      change (c : ℂ) * Section1.degree η2 + (a : ℂ) * Section1.degree φ = 0
      rw [hη2Degree, ← hanchorDegree, hχDegree]
      ring
    have hAgree1 : T1 η1zero = T η1zero :=
      hExt1.2.2 η1zero ⟨hη1zeroSpan, hη1zeroOn⟩
    have hAgree2 : T2 η2zero = T η2zero :=
      hExt2.2.2 η2zero ⟨hη2zeroSpan, hη2zeroOn⟩
    have hTnew1 : Tnew η1 = T1 η1 := by
      calc
        Tnew η1 = Section1.evalCoeff
            (fun X : S1 => Tnew (X : Section1.ClassFunction L)) v1 := by
              exact map_evalCoeff_pf57 Tnew _ v1
        _ = Section1.evalCoeff
            (fun X : S1 => T1 (X : Section1.ClassFunction L)) v1 := by
              congr 1
              funext X
              simpa only [img, dif_pos X.2] using
                hTnew ⟨X, Finset.mem_union_left S2 X.2⟩
        _ = T1 η1 := by
              exact (map_evalCoeff_pf57 T1 _ v1).symm
    have hTnew2 : Tnew η2 = T2 η2 := by
      calc
        Tnew η2 = Section1.evalCoeff
            (fun X : S2 => Tnew (X : Section1.ClassFunction L)) v2 := by
              exact map_evalCoeff_pf57 Tnew _ v2
        _ = Section1.evalCoeff
            (fun X : S2 => T2 (X : Section1.ClassFunction L)) v2 := by
              congr 1
              funext X
              have hXnot : (X : Section1.ClassFunction L) ∉ S1 := by
                intro hX1
                exact Finset.disjoint_left.mp hdisjoint hX1 X.2
              simpa only [img, dif_neg hXnot] using
                hTnew ⟨X, Finset.mem_union_right S1 X.2⟩
        _ = T2 η2 := by
              exact (map_evalCoeff_pf57 T2 _ v2).symm
    have hscaled :
        (c : ℂ) • (T1 η1 + T2 η2) = (c : ℂ) • T (η1 + η2) := by
      calc
        (c : ℂ) • (T1 η1 + T2 η2) =
            (T1 η1zero + (a : ℂ) • T1 χ) +
              (T2 η2zero - (a : ℂ) • T2 φ) := by
                dsimp [η1zero, η2zero]
                simp only [map_sub, map_add, map_smul]
                module
        _ = (T η1zero + (a : ℂ) • T1 χ) +
              (T η2zero - (a : ℂ) • T2 φ) := by
                rw [hAgree1, hAgree2]
        _ = (c : ℂ) • T (η1 + η2) +
              (a : ℂ) • ((T1 χ - T2 φ) - T (χ - φ)) := by
                dsimp [η1zero, η2zero]
                simp only [map_sub, map_add, map_smul]
                module
        _ = (c : ℂ) • T (η1 + η2) := by
                rw [hanchor]
                simp
    have hscaledDiff : (c : ℂ) • (Tnew η - T η) = 0 := by
      rw [smul_sub, hηSplit, map_add, hTnew1, hTnew2, hscaled]
      simp
    have hdiff : Tnew η - T η = 0 :=
      (smul_eq_zero.mp hscaledDiff).resolve_left hc
    exact sub_eq_zero.mp hdiff
  have hsource : sourceVirtualCharacters U := by
    intro ξ hξ
    exact isVirtualCharacter_of_isCharacter (hsetup.2 ⟨ξ, hξ⟩)
  have hnonempty : integerSpanOnNonempty U puncturedSet :=
    integerSpanOnNonempty_of_conjugate_pair hχU
      (h52a ⟨χ, hχU⟩).1 (h52a ⟨χ, hχU⟩).2
      (hsetup.2 ⟨χ, hχU⟩)
  rcases exists_extension_fields_of_image_family_pf57 U T img h52c hselfNe
      himgVirt himgGram hagree with ⟨Tnew, hIso, hVirt, hAgree⟩
  exact ⟨hsource, hnonempty, Tnew, hIso, hVirt, hAgree⟩

end CFSG.Section5

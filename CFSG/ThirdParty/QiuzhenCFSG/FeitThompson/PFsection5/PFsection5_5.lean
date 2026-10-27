module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 5, Theorem (5.5)

This file isolates PF `(5.5)` as its own proof target.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section5

universe v
universe u

/-! ## (5.5) -/

/--
Peterfalvi `(5.5)`: under Hypothesis `(5.2)`, any isometry `T₁` on `Z[X, X̄]`
which agrees with `T` on `Z[X - X̄]` sends `X` to a subset-sum of `R(X)`.
-/
@[expose] public def theorem_5_5_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G)) : Prop :=
  hypothesis_5_2_setup_statement S →
    hypothesis_5_2_a_statement S →
      hypothesis_5_2_b_statement S T →
        hypothesis_5_2_c_statement S →
          hypothesis_5_2_d_statement S T R →
            hypothesis_5_2_e_statement S R →
              ∀ X : S,
                ∀ T1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
                  isCFLinearIsometryOnSpan
                      ({(X : Section1.ClassFunction L),
                        Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
                        Finset (Section1.ClassFunction L)) T1 →
                    mapsIntegerSpanToVirtualCharacters
                        ({(X : Section1.ClassFunction L),
                          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
                          Finset (Section1.ClassFunction L)) T1 →
                      T1 ((X : Section1.ClassFunction L) -
                            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
                        T ((X : Section1.ClassFunction L) -
                            Section1.conjugateCharacter (X : Section1.ClassFunction L)) →
                        isSubsetSumOf (R X) (T1 (X : Section1.ClassFunction L))


private theorem scalarProduct_zero_swap_pf55
    {H : Type*} [Finite H]
    {φ ψ : Section1.ClassFunction H}
    (h : Section1.scalarProduct H φ ψ = 0) :
    Section1.scalarProduct H ψ φ = 0 := by
  simpa [Section1.scalarProduct_star_swap] using congrArg star h

private theorem scalarProduct_add_right_pf55
    {H : Type*} [Finite H]
    (φ ψ1 ψ2 : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ1 + ψ2) =
      Section1.scalarProduct H φ ψ1 + Section1.scalarProduct H φ ψ2 := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_sub_right_pf55
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
            rw [scalarProduct_add_right_pf55]
    _ = Section1.scalarProduct H φ ψ1 - Section1.scalarProduct H φ ψ2 := by
          rw [Section1.scalarProduct_smul_right]
          simp [sub_eq_add_neg]

private theorem scalarProduct_sub_left_pf55
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

private theorem scalarProduct_self_of_irreducibleCharacterOnGroup_pf55
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  simpa using Section1.scalarProduct_representation_char_self ρ hρ

private theorem scalarProduct_self_of_signedIrreducible_pf55
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμself : Section1.scalarProduct G μ μ = 1 :=
    scalarProduct_self_of_irreducibleCharacterOnGroup_pf55 hμ
  rcases hε with rfl | rfl
  · simp [hμself]
  · calc
      Section1.scalarProduct G ((-1 : ℂ) • μ) ((-1 : ℂ) • μ)
          = (-1 : ℂ) * (star (-1 : ℂ)) * Section1.scalarProduct G μ μ := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
              ring
      _ = 1 := by simp [hμself]

private theorem scalarProduct_eq_ite_of_signedOrthonormalFinset_pf55
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R) :
    ∀ a b : R, Section1.scalarProduct G (a : Section1.ClassFunction G) b =
      if a = b then 1 else 0 := by
  intro a b
  by_cases hab : a = b
  · subst hab
    simpa using scalarProduct_self_of_signedIrreducible_pf55 (hR.1 _ a.2)
  · simpa [hab] using hR.2 a.2 b.2 (fun hEq => hab (Subtype.ext hEq))

private theorem scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf55
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

private theorem integerSpan_of_mem_pf55
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

private theorem orthogonalToFinset_scalarProduct_evalCoeff_zero_pf55
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

private theorem cfNormSq_sub_eq_add_of_orthogonal_pf55
    {H : Type*} [Group H] [Finite H]
    {φ ψ : Section1.ClassFunction H}
    (hφψ : Section1.scalarProduct H φ ψ = 0)
    (hψφ : Section1.scalarProduct H ψ φ = 0) :
    cfNormSq (φ - ψ) = cfNormSq φ + cfNormSq ψ := by
  unfold cfNormSq
  rw [scalarProduct_sub_left_pf55, scalarProduct_sub_right_pf55, scalarProduct_sub_right_pf55]
  simp [hφψ, hψφ]

private theorem int_mul_pred_nonneg_pf55 (n : Int) :
    0 ≤ n * (n - 1) := by
  rcases le_or_gt n 0 with hn | hn
  · have hpred : n - 1 ≤ 0 := by omega
    exact mul_nonneg_of_nonpos_of_nonpos hn hpred
  · have hnonneg : 0 ≤ n := le_of_lt hn
    have hpred : 0 ≤ n - 1 := by omega
    exact mul_nonneg hnonneg hpred

private theorem int_cast_le_sq_pf55 (n : Int) :
    (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
  have hnonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    exact_mod_cast int_mul_pred_nonneg_pf55 n
  nlinarith

private theorem int_cast_sq_sub_self_nonneg_pf55 (n : Int) :
    0 ≤ (n : ℝ) * (n : ℝ) - (n : ℝ) := by
  have hnonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    exact_mod_cast int_mul_pred_nonneg_pf55 n
  nlinarith

private theorem cfNormSq_eq_inv_card_mul_sum_normSq_pf55
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

private theorem cfNormSq_nonneg_pf55
    {H : Type*} [Group H] [Finite H]
    (φ : Section1.ClassFunction H) :
    0 ≤ cfNormSq φ := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf55]
  have hcard : 0 ≤ (Nat.card H : ℝ)⁻¹ := by positivity
  have hsum : 0 ≤ ∑ g : H, Complex.normSq (φ g) := by
    refine Finset.sum_nonneg ?_
    intro g _hg
    exact Complex.normSq_nonneg (φ g)
  exact mul_nonneg hcard hsum

private theorem cfNormSq_eq_zero_pf55
    {H : Type*} [Group H] [Finite H]
    {φ : Section1.ClassFunction H}
    (hφ : cfNormSq φ = 0) :
    φ = 0 := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf55] at hφ
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

private theorem isVirtualCharacter_of_signedIrreducible_pf55
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Theory.Character.IsVirtualCharacter χ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hμ
  · simpa using Section3.isVirtualCharacter_neg
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hμ)

public theorem theorem_5_5_core_on_pair
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (h52a : hypothesis_5_2_a_statement S)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (X : S)
    (pair : Finset (Section1.ClassFunction L))
    (T1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hpairX : integerSpan pair (X : Section1.ClassFunction L))
    (hpairDiff : integerSpan pair
      ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)))
    (hIso : isCFLinearIsometryOnSpan pair T1)
    (hT1virt : mapsIntegerSpanToVirtualCharacters pair T1)
    (hagree :
      T1 ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        T ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L))) :
    isSubsetSumOf (R X) (T1 (X : Section1.ClassFunction L)) := by
  let Xbar : S := ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩
  rcases h52d X with ⟨hR, hTdiff⟩
  let μ : R X → Section1.ClassFunction G := fun a => (a : Section1.ClassFunction G)
  have hμorth :
      ∀ a b : R X,
        Section1.scalarProduct G (μ a) (μ b) = if a = b then 1 else 0 :=
    scalarProduct_eq_ite_of_signedOrthonormalFinset_pf55 hR
  have hμbasis :
      ∀ r : R X, Section1.evalCoeff μ (Section1.basisVector r) = μ r := by
    intro r
    ext g
    rw [Section1.evalCoeff, Finset.sum_eq_single r]
    · simp [Section1.basisVector]
    · intro s _hs hsr
      simp [Section1.basisVector, hsr]
    · intro hrFalse
      exact (hrFalse (Finset.mem_univ _)).elim
  have hT1Xvirt : Theory.Character.IsVirtualCharacter (T1 (X : Section1.ClassFunction L)) := by
    exact hT1virt _ hpairX
  let a : Section1.CoeffVector (R X) := fun r =>
    Classical.choose <|
      Section3.scalarProduct_isVirtualCharacter_eq_int
        hT1Xvirt
        (isVirtualCharacter_of_signedIrreducible_pf55 (hR.1 _ r.2))
  have ha :
      ∀ r : R X,
        Section1.scalarProduct G
            (T1 (X : Section1.ClassFunction L))
            (μ r) =
          (a r : ℂ) := by
    intro r
    exact Classical.choose_spec <|
      Section3.scalarProduct_isVirtualCharacter_eq_int
        hT1Xvirt
        (isVirtualCharacter_of_signedIrreducible_pf55 (hR.1 _ r.2))
  let Xbig : Section1.ClassFunction G := Section1.evalCoeff μ a
  let Y : Section1.ClassFunction G := Xbig - T1 (X : Section1.ClassFunction L)
  have hXbigspan : integerSpan (R X) Xbig := by
    refine ⟨a, rfl⟩
  have hYorth : orthogonalToFinset (R X) Y := by
    intro ψ hψ
    let r : R X := ⟨ψ, hψ⟩
    have hXbigCoeff :
        Section1.scalarProduct G Xbig (μ r) = (a r : ℂ) := by
      rw [← hμbasis r]
      dsimp [Xbig]
      calc
        Section1.scalarProduct G
            (Section1.evalCoeff μ a)
            (Section1.evalCoeff μ (Section1.basisVector r)) =
            (Section1.coeffDot a (Section1.basisVector r) : ℂ) := by
              simpa using
                scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf55
                  μ hμorth a (Section1.basisVector r)
        _ = (a r : ℂ) := by
              simp [Section1.coeffDot, Section1.basisVector]
    have hT1Coeff :
        Section1.scalarProduct G
            (T1 (X : Section1.ClassFunction L))
            (μ r) =
          (a r : ℂ) := ha r
    dsimp [Y]
    rw [scalarProduct_sub_left_pf55]
    simpa [μ] using sub_eq_zero.mpr (hXbigCoeff.trans hT1Coeff.symm)
  have hYXbigZero :
      Section1.scalarProduct G Y Xbig = 0 := by
    dsimp [Xbig]
    exact orthogonalToFinset_scalarProduct_evalCoeff_zero_pf55 μ
      (fun r => hYorth r.2) a
  have hXbigYZero :
      Section1.scalarProduct G Xbig Y = 0 :=
    scalarProduct_zero_swap_pf55 hYXbigZero
  have hXXbarZero :
      Section1.scalarProduct L
          (X : Section1.ClassFunction L)
          (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0 := by
    exact h52c (χ := (X : Section1.ClassFunction L))
      (ψ := (Xbar : Section1.ClassFunction L)) X.2 Xbar.2
      (by simpa [Xbar] using (h52a X).2)
  let oneVec : Section1.CoeffVector (R X) := fun _ => 1
  have hsumEval :
      Section1.evalCoeff μ oneVec = Finset.sum (R X) fun φ => φ := by
    ext g
    simp [Section1.evalCoeff, μ, oneVec]
    simpa using
      (Finset.sum_attach (R X) fun c : Section1.ClassFunction G => c g)
  have hsourcePair :
      Section1.scalarProduct L
          (X : Section1.ClassFunction L)
          ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        Section1.scalarProduct L (X : Section1.ClassFunction L) (X : Section1.ClassFunction L) := by
    rw [scalarProduct_sub_right_pf55]
    simp [hXXbarZero]
  have hpairEval :
      Section1.scalarProduct L
          (X : Section1.ClassFunction L)
          ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        (Section1.coeffDot a oneVec : ℂ) := by
    calc
      Section1.scalarProduct L
          (X : Section1.ClassFunction L)
          ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        Section1.scalarProduct G
          (T1 (X : Section1.ClassFunction L))
          (T1 ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L))) := by
            symm
            exact hIso _ _ hpairX hpairDiff
      _ = Section1.scalarProduct G
            (T1 (X : Section1.ClassFunction L))
            (Section1.evalCoeff μ oneVec) := by
              rw [hagree, hTdiff, ← hsumEval]
      _ = (Section1.coeffDot a oneVec : ℂ) := by
            have hright :
                (∑ j : R X, (oneVec j : ℂ) • μ j) =
                  (fun g : G => ∑ j : R X, ((oneVec j : ℂ) • μ j) g) := by
              ext g
              simp
            rw [Section1.evalCoeff, hright, Section1.scalarProduct_fintype_sum_right]
            simp_rw [Section1.scalarProduct_smul_right, ha]
            simp [Section1.coeffDot, oneVec]
  have hcfX :
      cfNormSq (X : Section1.ClassFunction L) = (Section1.coeffDot a oneVec : ℝ) := by
    unfold cfNormSq
    rw [← hsourcePair, hpairEval]
    simp
  have hcfXbig :
      cfNormSq Xbig = (Section1.coeffDot a a : ℝ) := by
    unfold cfNormSq Xbig
    rw [scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf55 μ hμorth]
    simp
  have hcoeff_le :
      ((Section1.coeffDot a oneVec : ℤ) : ℝ) ≤ ((Section1.coeffDot a a : ℤ) : ℝ) := by
    have hsum :
        (∑ r : R X, (a r : ℝ)) ≤ ∑ r : R X, (a r : ℝ) * (a r : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro r _hr
      exact int_cast_le_sq_pf55 (a r)
    simpa [Section1.coeffDot, oneVec, Int.cast_sum, Int.cast_mul] using hsum
  have hXbig_ge :
      cfNormSq Xbig ≥ cfNormSq (X : Section1.ClassFunction L) := by
    linarith [hcfX, hcfXbig, hcoeff_le]
  have hT1Norm :
      cfNormSq (T1 (X : Section1.ClassFunction L)) =
        cfNormSq (X : Section1.ClassFunction L) := by
    have hIsoNorm := hIso (X : Section1.ClassFunction L) (X : Section1.ClassFunction L) hpairX hpairX
    simpa [cfNormSq] using congrArg Complex.re hIsoNorm
  have htargetNorm :
      cfNormSq (Xbig - Y) = cfNormSq Xbig + cfNormSq Y := by
    exact cfNormSq_sub_eq_add_of_orthogonal_pf55 hXbigYZero hYXbigZero
  have hEq :
      T1 (X : Section1.ClassFunction L) = Xbig - Y := by
    dsimp [Y]
    ext g
    simp
  have hsumNorm :
      cfNormSq Xbig + cfNormSq Y = cfNormSq (X : Section1.ClassFunction L) := by
    calc
      cfNormSq Xbig + cfNormSq Y = cfNormSq (Xbig - Y) := by
        symm
        exact htargetNorm
      _ = cfNormSq (T1 (X : Section1.ClassFunction L)) := by
        rw [← hEq]
      _ = cfNormSq (X : Section1.ClassFunction L) := hT1Norm
  have hYnonneg : 0 ≤ cfNormSq Y := cfNormSq_nonneg_pf55 Y
  have hYZeroNorm : cfNormSq Y = 0 := by
    linarith [hsumNorm, hXbig_ge, hYnonneg]
  have hYZero : Y = 0 := cfNormSq_eq_zero_pf55 hYZeroNorm
  have hXbigEq : Xbig = T1 (X : Section1.ClassFunction L) := by
    simpa [hYZero] using hEq.symm
  have hcoeffEq :
      ((Section1.coeffDot a a : ℤ) : ℝ) = ((Section1.coeffDot a oneVec : ℤ) : ℝ) := by
    have hXbigNorm :
        cfNormSq Xbig = cfNormSq (X : Section1.ClassFunction L) := by
      calc
        cfNormSq Xbig = cfNormSq (T1 (X : Section1.ClassFunction L)) := by
          simp [hXbigEq]
        _ = cfNormSq (X : Section1.ClassFunction L) := hT1Norm
    linarith [hcfX, hcfXbig, hXbigNorm]
  let Esub : Finset (R X) := Finset.univ.filter fun r => a r = 1
  have hcoeff01 : ∀ r : R X, a r = 0 ∨ a r = 1 := by
    intro r
    have hcoeffEq' :
        (∑ s : R X, (a s : ℝ) * (a s : ℝ)) = ∑ s : R X, (a s : ℝ) := by
      simpa [Section1.coeffDot, oneVec, Int.cast_sum, Int.cast_mul] using hcoeffEq
    have hsumZero :
        ∑ s : R X, ((a s : ℝ) * (a s : ℝ) - (a s : ℝ)) = 0 := by
      rw [Finset.sum_sub_distrib, hcoeffEq']
      ring
    have hnonneg :
        ∀ s ∈ (Finset.univ : Finset (R X)),
          0 ≤ (a s : ℝ) * (a s : ℝ) - (a s : ℝ) := by
      intro s _hs
      exact int_cast_sq_sub_self_nonneg_pf55 (a s)
    have hzeroAll :
        ∀ s ∈ (Finset.univ : Finset (R X)),
          (a s : ℝ) * (a s : ℝ) - (a s : ℝ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsumZero
    have hz : (a r : ℝ) * (a r : ℝ) - (a r : ℝ) = 0 := hzeroAll r (by simp)
    have hfac : (a r : ℝ) * ((a r : ℝ) - 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with hr0 | hr1
    · left
      exact_mod_cast hr0
    · right
      have hr1' : (a r : ℝ) = 1 := by
        linarith
      exact_mod_cast hr1'
  have hXbigSubset :
      Xbig = Finset.sum Esub fun r => (r : Section1.ClassFunction G) := by
    have ha_indicator :
        a = fun r => if r ∈ Esub then 1 else 0 := by
      funext r
      by_cases hr : r ∈ Esub
      · have har : a r = 1 := by
          simpa [Esub] using hr
        simp [hr, har]
      · have harnot : a r ≠ 1 := by
          simpa [Esub] using hr
        rcases hcoeff01 r with hr0 | hr1
        · simp [hr, hr0]
        · exact False.elim (harnot hr1)
    rw [show Xbig = Section1.evalCoeff μ a by rfl, ha_indicator]
    ext g
    simp [Section1.evalCoeff, Esub, μ, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    by_cases h : a r = 1 <;> simp [h]
  refine ⟨Esub.image (fun r : R X => (r : Section1.ClassFunction G)), ?_, ?_⟩
  · intro φ hφ
    rcases Finset.mem_image.mp hφ with ⟨r, _hr, rfl⟩
    exact r.2
  · calc
      T1 (X : Section1.ClassFunction L) = Xbig := hXbigEq.symm
      _ = Finset.sum Esub fun r => (r : Section1.ClassFunction G) := hXbigSubset
      _ = Finset.sum (Esub.image (fun r : R X => (r : Section1.ClassFunction G))) fun φ => φ := by
            symm
            exact Finset.sum_image
              (s := Esub)
              (g := fun r : R X => (r : Section1.ClassFunction G))
              (f := fun φ => φ)
              (by
                intro r _hr s _hs hrs
                exact Subtype.ext hrs)

public theorem theorem_5_5_core
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (h52a : hypothesis_5_2_a_statement S)
    (h52c : hypothesis_5_2_c_statement S)
    (h52d : hypothesis_5_2_d_statement S T R)
    (X : S)
    (T1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hIso : isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L)) T1)
    (hT1virt : mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L)) T1)
    (hagree :
      T1 ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        T ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L))) :
    isSubsetSumOf (R X) (T1 (X : Section1.ClassFunction L)) := by
  let pair : Finset (Section1.ClassFunction L) :=
    {(X : Section1.ClassFunction L),
      Section1.conjugateCharacter (X : Section1.ClassFunction L)}
  have hpairX : integerSpan pair (X : Section1.ClassFunction L) := by
    apply integerSpan_of_mem_pf55
    simp [pair]
  have hpairDiff :
      integerSpan pair
        ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
    let xPair : pair := ⟨(X : Section1.ClassFunction L), by simp [pair]⟩
    let xbarPair : pair :=
      ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), by simp [pair]⟩
    refine ⟨Section1.signedBasisDifference 1 xbarPair xPair, ?_⟩
    ext g
    simpa [xPair, xbarPair, pair, Section1.signIntToComplex] using
      (congrArg (fun f : Section1.ClassFunction L => f g)
        (Section1.evalCoeff_signedBasisDifference
          (G := L) (J := pair)
          (mu := fun y : pair => (y : Section1.ClassFunction L))
          1 xbarPair xPair)).symm
  exact theorem_5_5_core_on_pair S T R h52a h52c h52d X pair T1
    hpairX hpairDiff hIso hT1virt hagree

public theorem theorem_5_5
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G)) :
    theorem_5_5_statement S T R := by
  intro _hsetup h52a _h52b h52c h52d _h52e X T1 hIso hT1virt hagree
  exact theorem_5_5_core S T R h52a h52c h52d X T1 hIso hT1virt hagree

end CFSG.Section5

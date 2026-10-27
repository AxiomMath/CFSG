module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_17

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_18
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.18) -/


private def theorem_13_18_betaData
    {G : Type u} [Group G] [Finite G]
    (Smax W W1 W2 P : Subgroup G)
    (βS : Section1.ClassFunction Smax)
    (q u : ℕ) : Prop :=
  Section1.supportedOn βS
      (subgroupSetPreimage Smax
        ((section16NonidentityElements (P : Set G)) ∪
          section16ConjugatesOfSetBySet
            ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (Smax : Set G))) ∧
    Section1.supportedOn βS (subgroupSetPreimage Smax (typePFAZeroSet Smax W1 W2 P)) ∧
    Section5.cfNormSq βS = ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 2

private def theorem_13_18_gammaData
    {G : Type u} [Group G] [Finite G]
    (Smax P W1 : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (Γ : Section1.ClassFunction G)
    (p : ℕ) : Prop :=
  (∀ k : ℕ, 0 < k → k < p →
    ∃ (μ0k βSk : Section1.ClassFunction Smax) (βτk : Section1.ClassFunction G),
      theorem_13_18_hypothesis Smax P W1 μ0k βSk k p ∧
        βτk = τS βSk ∧
        Γ = βτk - Section1.principalCharacter G + η 0 k) ∧
    Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0 ∧
    Γ = Section1.conjugateCharacter Γ

private def theorem_13_18_decompositionNormData
    {G : Type u} [Group G] [Finite G]
    (p q u : ℕ)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (Γ X Y : Section1.ClassFunction G) : Prop :=
  Γ = X + Y ∧
    theorem_13_18_decompositionData p q η X Y ∧
    Section5.cfNormSq Y ≤ ((u - 1 : ℕ) : ℝ) / (q : ℝ)

private theorem theorem_13_18_scalarProduct_finset_sum_left
    {G ι : Type*} [Finite G]
    (s : Finset ι) (Φ : ι → Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (s.sum Φ) ψ =
      s.sum (fun i => Section1.scalarProduct G (Φ i) ψ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | insert a s ha ih =>
      simp [Finset.sum_insert ha, Section1.scalarProduct_add_left, ih]

private theorem theorem_13_18_scalarProduct_finset_sum_right
    {G ι : Type*} [Finite G]
    (s : Finset ι) (φ : Section1.ClassFunction G)
    (Ψ : ι → Section1.ClassFunction G) :
    Section1.scalarProduct G φ (s.sum Ψ) =
      s.sum (fun i => Section1.scalarProduct G φ (Ψ i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | insert a s ha ih =>
      simp [Finset.sum_insert ha, Section5.scalarProduct_add_right, ih]

private theorem theorem_13_18_scalarProduct_sub_left
    {G : Type*} [Finite G]
    (φ ψ χ : Section1.ClassFunction G) :
    Section1.scalarProduct G (φ - ψ) χ =
      Section1.scalarProduct G φ χ - Section1.scalarProduct G ψ χ :=
  Section5.scalarProduct_sub_left φ ψ χ

private theorem theorem_13_18_cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq
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

public theorem theorem_13_18_finite_orthonormal_coeff_normSq_sum_le_cfNormSq
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
    exact theorem_13_18_cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq w χ horth
  simpa [w, hPnorm] using hPnorm_le

private theorem theorem_13_18_int_quadratic_two_le (a : ℤ) :
    (2 : ℝ) ≤ 1 + ((a : ℝ) - 1) ^ 2 + (a : ℝ) ^ 2 := by
  have h : (1 : ℝ) ≤ ((a : ℝ) - 1) ^ 2 + (a : ℝ) ^ 2 := by
    by_cases ha : a ≤ 0
    · have hle : (a : ℝ) ≤ 0 := by exact_mod_cast ha
      have hge : (1 : ℝ) ≤ ((a : ℝ) - 1) ^ 2 := by
        nlinarith [sq_nonneg ((a : ℝ) - 1)]
      have hnonneg : 0 ≤ (a : ℝ) ^ 2 := sq_nonneg (a : ℝ)
      nlinarith
    · have hgeInt : 1 ≤ a := by omega
      have hge : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hgeInt
      have hsq : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((a : ℝ) - 1)]
      have hnonneg : 0 ≤ ((a : ℝ) - 1) ^ 2 := sq_nonneg ((a : ℝ) - 1)
      nlinarith
  nlinarith

private theorem theorem_13_18_three_coeff_lower_bound
    {G : Type*} [Group G] [Finite G]
    (χ0 χ1 χ2 φ : Section1.ClassFunction G) (a : ℤ)
    (h00 : Section1.scalarProduct G χ0 χ0 = 1)
    (h11 : Section1.scalarProduct G χ1 χ1 = 1)
    (h22 : Section1.scalarProduct G χ2 χ2 = 1)
    (h01 : Section1.scalarProduct G χ0 χ1 = 0)
    (h10 : Section1.scalarProduct G χ1 χ0 = 0)
    (h02 : Section1.scalarProduct G χ0 χ2 = 0)
    (h20 : Section1.scalarProduct G χ2 χ0 = 0)
    (h12 : Section1.scalarProduct G χ1 χ2 = 0)
    (h21 : Section1.scalarProduct G χ2 χ1 = 0)
    (h0 : Section1.scalarProduct G φ χ0 = 1)
    (h1 : Section1.scalarProduct G φ χ1 = (a : ℂ) - 1)
    (h2 : Section1.scalarProduct G φ χ2 = (a : ℂ)) :
    (2 : ℝ) ≤ Section5.cfNormSq φ := by
  let c0 : ℂ := Section1.scalarProduct G φ χ0
  let c1 : ℂ := Section1.scalarProduct G φ χ1
  let c2 : ℂ := Section1.scalarProduct G φ χ2
  let P0 : Section1.ClassFunction G := c0 • χ0
  let P1 : Section1.ClassFunction G := c1 • χ1
  let P2 : Section1.ClassFunction G := c2 • χ2
  let P : Section1.ClassFunction G := P0 + P1 + P2
  let R : Section1.ClassFunction G := φ - P
  have hR0 : Section1.scalarProduct G R χ0 = 0 := by
    dsimp [R, P, P0, P1, P2, c0, c1, c2]
    rw [Section5.scalarProduct_sub_left, Section1.scalarProduct_add_left,
      Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
    rw [h00, h10, h20]
    ring
  have hR1 : Section1.scalarProduct G R χ1 = 0 := by
    dsimp [R, P, P0, P1, P2, c0, c1, c2]
    rw [Section5.scalarProduct_sub_left, Section1.scalarProduct_add_left,
      Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
    rw [h01, h11, h21]
    ring
  have hR2 : Section1.scalarProduct G R χ2 = 0 := by
    dsimp [R, P, P0, P1, P2, c0, c1, c2]
    rw [Section5.scalarProduct_sub_left, Section1.scalarProduct_add_left,
      Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
    rw [h02, h12, h22]
    ring
  have hRP : Section1.scalarProduct G R P = 0 := by
    dsimp [P, P0, P1, P2]
    rw [Section5.scalarProduct_add_right, Section5.scalarProduct_add_right,
      Section1.scalarProduct_smul_right, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_right]
    rw [hR0, hR1, hR2]
    simp
  have hPR : Section1.scalarProduct G P R = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRP
  have hφdecomp : φ = R + P := by
    dsimp [R, P]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
  have hφnorm : Section5.cfNormSq φ = Section5.cfNormSq R + Section5.cfNormSq P := by
    rw [hφdecomp]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hRP hPR
  have hP0P1 : Section1.scalarProduct G P0 P1 = 0 := by
    dsimp [P0, P1]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, h01]
    simp
  have hP1P0 : Section1.scalarProduct G P1 P0 = 0 := by
    dsimp [P0, P1]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, h10]
    simp
  have hP01P2 : Section1.scalarProduct G (P0 + P1) P2 = 0 := by
    dsimp [P0, P1, P2]
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_right]
    rw [h02, h12]
    simp
  have hP2P01 : Section1.scalarProduct G P2 (P0 + P1) = 0 := by
    dsimp [P0, P1, P2]
    rw [Section5.scalarProduct_add_right, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_right, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_right]
    rw [h20, h21]
    simp
  have hPnorm :
      Section5.cfNormSq P = Complex.normSq c0 + Complex.normSq c1 + Complex.normSq c2 := by
    dsimp [P]
    rw [Section5.cfNormSq_add_eq_add_of_orthogonal hP01P2 hP2P01]
    rw [Section5.cfNormSq_add_eq_add_of_orthogonal hP0P1 hP1P0]
    dsimp [P0, P1, P2]
    rw [Section5.cfNormSq_smul, Section5.cfNormSq_smul, Section5.cfNormSq_smul]
    unfold Section5.cfNormSq
    rw [h00, h11, h22]
    simp
  have hcoeff :
      Complex.normSq c0 + Complex.normSq c1 + Complex.normSq c2 =
        1 + ((a : ℝ) - 1) ^ 2 + (a : ℝ) ^ 2 := by
    dsimp [c0, c1, c2]
    rw [h0, h1, h2]
    norm_num [Complex.normSq]
    ring
  have hP_le : Section5.cfNormSq P ≤ Section5.cfNormSq φ := by
    have hRnonneg : 0 ≤ Section5.cfNormSq R := Section5.cfNormSq_nonneg R
    nlinarith
  rw [hPnorm, hcoeff] at hP_le
  exact (theorem_13_18_int_quadratic_two_le a).trans hP_le

private theorem theorem_13_18_conjugateCharacter_involutive
    {G : Type*} (φ : Section1.ClassFunction G) :
    Section1.conjugateCharacter (Section1.conjugateCharacter φ) = φ := by
  ext g
  simp [Section1.conjugateCharacter]

private theorem theorem_13_18_scalarProduct_conjugate_left
    {G : Type*} [Finite G] (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Section1.conjugateCharacter φ) ψ =
      star (Section1.scalarProduct G φ (Section1.conjugateCharacter ψ)) := by
  simp [Section1.scalarProduct, Section1.conjugateCharacter]

private theorem theorem_13_18_decomposition_scalarProduct_Y_X_eq_zero
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ} {η : ℕ → ℕ → Section1.ClassFunction G}
    {X Y : Section1.ClassFunction G}
    (hdecomp : theorem_13_18_decompositionData p q η X Y) :
    Section1.scalarProduct G Y X = 0 := by
  classical
  rcases hdecomp with ⟨⟨coeff, hX⟩, hYη⟩
  rw [hX]
  rw [theorem_13_18_scalarProduct_finset_sum_right]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [theorem_13_18_scalarProduct_finset_sum_right]
  refine Finset.sum_eq_zero ?_
  intro k hk
  rw [Section1.scalarProduct_smul_right]
  rw [hYη i k (Finset.mem_range.mp hi) (Finset.mem_range.mp hk)]
  simp


public theorem theorem_13_18_scalarProduct_principalCharacter_self
    {G : Type u} [Group G] [Finite G] :
    Section1.scalarProduct G (Section1.principalCharacter G)
      (Section1.principalCharacter G) = 1 := by
  classical
  simp [Section1.scalarProduct, Section1.principalCharacter]

public theorem theorem_13_18_eta_zero_row_principal_orthogonal_of_notation
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
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) :
    hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
      ∀ k : ℕ, 0 < k → k < p →
        Section1.scalarProduct G (η 0 k) (Section1.principalCharacter G) = 0 := by
  intro hnotation k hk0 hkp
  rcases hnotation with
    ⟨hωData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, hppos, ωFin, hωFin, hωNat⟩
  rcases hσmap with
    ⟨hσiso, _hσvirt, _hσind, _hσclass, hσprincipal, _hσcyc, _hσvanish⟩
  let fi0 : Fin q := ⟨0, hqpos⟩
  let fk0 : Fin p := ⟨0, hppos⟩
  let fk : Fin p := ⟨k, hkp⟩
  have hη0k : η 0 k = σ (ωFin fi0 fk) := by
    rw [hη 0 k hqpos hkp, hωNat 0 k hqpos hkp]
  have hprincipal : σ (ωFin fi0 fk0) = Section1.principalCharacter G := by
    rw [hωFin.principal, hσprincipal]
  have hpair_ne : (fi0, fk) ≠ (fi0, fk0) := by
    intro hpair
    have hk_eq_zero : k = 0 :=
      congrArg (fun x : Fin p => (x : ℕ)) (Prod.ext_iff.mp hpair).2
    exact (Nat.ne_of_gt hk0) hk_eq_zero
  calc
    Section1.scalarProduct G (η 0 k) (Section1.principalCharacter G)
        = Section1.scalarProduct G (σ (ωFin fi0 fk)) (σ (ωFin fi0 fk0)) := by
          rw [hη0k, hprincipal]
    _ = Section1.scalarProduct W (ωFin fi0 fk) (ωFin fi0 fk0) :=
          hσiso (ωFin fi0 fk) (ωFin fi0 fk0)
            (hωFin.is_class fi0 fk) (hωFin.is_class fi0 fk0)
    _ = 0 := by
          rw [Section3.isOrthonormalDoubleFamily_apply hωFin.orthonormal
            (fi0, fk) (fi0, fk0)]
          simp [hpair_ne]

private theorem theorem_13_18_eta_zero_zero_eq_principal_of_notation
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
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) :
    hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
      η 0 0 = Section1.principalCharacter G := by
  intro hnotation
  rcases hnotation with
    ⟨hωData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, hppos, ωFin, hωFin, hωNat⟩
  rcases hσmap with
    ⟨_hσiso, _hσvirt, _hσind, _hσclass, hσprincipal, _hσcyc, _hσvanish⟩
  let fi0 : Fin q := ⟨0, hqpos⟩
  let fk0 : Fin p := ⟨0, hppos⟩
  calc
    η 0 0 = σ (ωFin fi0 fk0) := by
      rw [hη 0 0 hqpos hppos, hωNat 0 0 hqpos hppos]
    _ = σ (Section1.principalCharacter W) := by
      rw [hωFin.principal]
    _ = Section1.principalCharacter G := hσprincipal

public theorem theorem_13_18_eta_virtual_of_notation
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
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) :
    hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
      ∀ i k : ℕ, i < q → k < p →
        Theory.Character.IsVirtualCharacter (η i k) := by
  intro hnotation i k hi hk
  rcases hnotation with
    ⟨hωData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωNat⟩
  rcases hσmap with
    ⟨_hσiso, hσvirt, _hσind, _hσclass, _hσprincipal, _hσcyc, _hσvanish⟩
  let fi : Fin q := ⟨i, hi⟩
  let fk : Fin p := ⟨k, hk⟩
  have hηik : η i k = σ (ωFin fi fk) := by
    rw [hη i k hi hk, hωNat i k hi hk]
  have hωvirt : Theory.Character.IsVirtualCharacter (ωFin fi fk) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hωFin.irreducible fi fk)
  rw [hηik]
  exact hσvirt (ωFin fi fk) hωvirt

private theorem theorem_13_18_isClassFunction_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨n, ρ, _hρ, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

private theorem theorem_13_18_irreducible_nonprincipal_principal_orthogonal
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχ_ne : χ ≠ Section1.principalCharacter G) :
    Section1.scalarProduct G χ (Section1.principalCharacter G) = 0 :=
  Section1.scalarProduct_isBookIrreducible_ne χ (Section1.principalCharacter G)
    (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hχ)
    (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      (Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := G)))
    hχ_ne

private theorem theorem_13_18_beta_isClassFunction_of_notation
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P : Subgroup G)
    (p q : ℕ)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j : ℕ) :
    hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
      theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
        Section1.IsClassFunction βS := by
  intro hnotation hβhyp
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  rcases hβhyp with ⟨_hj0, hjp, hβdef⟩
  have hμclass : Section1.IsClassFunction (μ 0 j) :=
    theorem_13_18_isClassFunction_of_irreducible (hμirr 0 j hqpos hjp)
  have hindClass :
      Section1.IsClassFunction
        (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) :=
    Section1.inducedCF_isClassFunction ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))
  rw [hβdef]
  intro x g
  simp [hindClass x g, hμclass x g]

public theorem theorem_13_18_eta_orthonormal_of_notation
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
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) :
    hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
      ∀ i k i' k' : ℕ, i < q → k < p → i' < q → k' < p →
        Section1.scalarProduct G (η i k) (η i' k') =
          if i = i' ∧ k = k' then 1 else 0 := by
  intro hnotation i k i' k' hi hk hi' hk'
  rcases hnotation with
    ⟨hωData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, hppos, ωFin, hωFin, hωNat⟩
  let fi : Fin q := ⟨i, hi⟩
  let fk : Fin p := ⟨k, hk⟩
  let fi' : Fin q := ⟨i', hi'⟩
  let fk' : Fin p := ⟨k', hk'⟩
  have hηik : η i k = σ (ωFin fi fk) := by
    rw [hη i k hi hk, hωNat i k hi hk]
  have hηi'k' : η i' k' = σ (ωFin fi' fk') := by
    rw [hη i' k' hi' hk', hωNat i' k' hi' hk']
  have hiso :
      Section1.scalarProduct G (σ (ωFin fi fk)) (σ (ωFin fi' fk')) =
        Section1.scalarProduct W (ωFin fi fk) (ωFin fi' fk') :=
    hσmap.1 (ωFin fi fk) (ωFin fi' fk') (hωFin.is_class fi fk)
      (hωFin.is_class fi' fk')
  have hωorth :=
    Section3.isOrthonormalDoubleFamily_apply hωFin.orthonormal
      (fi, fk) (fi', fk')
  rw [hηik, hηi'k', hiso, hωorth]
  by_cases hpair : i = i' ∧ k = k'
  · rcases hpair with ⟨rfl, rfl⟩
    have hfinPair : (fi, fk) = (fi', fk') := by
      ext <;> rfl
    simp [hfinPair]
  · have hfinPair : (fi, fk) ≠ (fi', fk') := by
      intro hfin
      apply hpair
      constructor
      · exact congrArg (fun x : Fin q => (x : ℕ)) (Prod.ext_iff.mp hfin).1
      · exact congrArg (fun x : Fin p => (x : ℕ)) (Prod.ext_iff.mp hfin).2
    simp [hpair, hfinPair]

private theorem theorem_13_18_projection_decomposition_of_eta_orthonormal
    {G : Type u} [Group G] [Finite G]
    (p q : ℕ)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (Γ : Section1.ClassFunction G)
    (hηorth : ∀ i k i' k' : ℕ, i < q → k < p → i' < q → k' < p →
      Section1.scalarProduct G (η i k) (η i' k') =
        if i = i' ∧ k = k' then 1 else 0) :
    ∃ X Y : Section1.ClassFunction G,
      Γ = X + Y ∧ theorem_13_18_decompositionData p q η X Y := by
  classical
  let coeff : ℕ → ℕ → ℂ := fun i k => Section1.scalarProduct G Γ (η i k)
  let X : Section1.ClassFunction G :=
    (Finset.range q).sum fun i =>
      (Finset.range p).sum fun k => coeff i k • η i k
  let Y : Section1.ClassFunction G := Γ - X
  refine ⟨X, Y, ?_, ?_⟩
  · ext g
    simp [Y, sub_eq_add_neg]
  · constructor
    · exact ⟨coeff, rfl⟩
    · intro i k hi hk
      have hXinner : Section1.scalarProduct G X (η i k) = coeff i k := by
        calc
          Section1.scalarProduct G X (η i k)
              = (Finset.range q).sum (fun i' =>
                  Section1.scalarProduct G
                    ((Finset.range p).sum fun k' => coeff i' k' • η i' k')
                    (η i k)) := by
                    simp [X, theorem_13_18_scalarProduct_finset_sum_left]
          _ = (Finset.range q).sum (fun i' =>
                  (Finset.range p).sum fun k' =>
                    coeff i' k' *
                      Section1.scalarProduct G (η i' k') (η i k)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i' _hi'
                    rw [theorem_13_18_scalarProduct_finset_sum_left]
                    refine Finset.sum_congr rfl ?_
                    intro k' _hk'
                    rw [Section1.scalarProduct_smul_left]
          _ = (Finset.range q).sum (fun i' =>
                  (Finset.range p).sum fun k' =>
                    coeff i' k' * (if i' = i ∧ k' = k then 1 else 0)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i' hi'
                    refine Finset.sum_congr rfl ?_
                    intro k' hk'
                    rw [hηorth i' k' i k (Finset.mem_range.mp hi')
                      (Finset.mem_range.mp hk') hi hk]
          _ = coeff i k := by
                    have hi_mem : i ∈ Finset.range q := Finset.mem_range.mpr hi
                    have hk_mem : k ∈ Finset.range p := Finset.mem_range.mpr hk
                    rw [Finset.sum_eq_single i]
                    · rw [Finset.sum_eq_single k]
                      · simp
                      · intro k' _hk' hk'ne
                        have hne : ¬ (i = i ∧ k' = k) := by
                          intro h
                          exact hk'ne h.2
                        rw [if_neg hne]
                        simp
                      · intro hknot
                        exact (hknot hk_mem).elim
                    · intro i' _hi' hi'ne
                      apply Finset.sum_eq_zero
                      intro k' _hk'
                      have hne : ¬ (i' = i ∧ k' = k) := by
                        intro h
                        exact hi'ne h.1
                      rw [if_neg hne]
                      simp
                    · intro hinot
                      exact (hinot hi_mem).elim
      dsimp [Y]
      rw [Section5.scalarProduct_sub_left, hXinner]
      ring

private theorem theorem_13_18_projection_decomposition_of_notation
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
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (Γ : Section1.ClassFunction G) :
    hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
      ∃ X Y : Section1.ClassFunction G,
        Γ = X + Y ∧ theorem_13_18_decompositionData p q η X Y := by
  intro hnotation
  exact theorem_13_18_projection_decomposition_of_eta_orthonormal p q η Γ
    (theorem_13_18_eta_orthonormal_of_notation Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ hnotation)


private def theorem_13_18_typeP_AZeroSetFromP
    {G : Type u} [Group G]
    (Smax W1 W2 P : Subgroup G) : Set G :=
  typePFAZeroSet Smax W1 W2 P

private theorem theorem_13_18_MF_le_derived_of_typeP
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 : Subgroup G}
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2) :
    P ≤ ambientDerivedSubgroup Smax := by
  rcases hTypeP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hComp, _hUleD, _hUnil,
      _hW1normU, _hDerComp, _hPnotCyc, _hSecondLe, hFittingEq, hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormHatW⟩
  intro x hx
  exact hFittingLeD (by
    rw [← hFittingEq]
    exact (le_sup_left : P ≤ P ⊔ subgroupCentralizerIn Smax P) hx)

private theorem theorem_13_18_betaSupport_subset_typeP_AZeroSetFromP
    {G : Type u} [Group G] [Finite G]
    {Smax W W1 W2 P U : Subgroup G}
    (hW : section12InternalDirectProduct W1 W2 W)
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2) :
    theorem_13_18_betaSupportSet Smax W W1 W2 P ⊆
      theorem_13_18_typeP_AZeroSetFromP Smax W1 W2 P := by
  classical
  intro x hx
  rcases hx with hxP | hxV
  · left
    refine ⟨x, hxP, ?_⟩
    refine ⟨?_, hxP.2⟩
    change x ∈ elementCentralizerIn (ambientDerivedSubgroup Smax) x
    rw [elementCentralizerIn]
    refine ⟨theorem_13_18_MF_le_derived_of_typeP hTypeP hxP.1, ?_⟩
    simp [Subgroup.mem_centralizer_iff]
  · right
    rcases hxV with ⟨w, hw, s, hs, rfl⟩
    refine ⟨w, ?_, s, hs, rfl⟩
    rcases hw with ⟨hwW, hwNot⟩
    change w ∈ (((W1 ⊔ W2 : Subgroup G) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))
    exact ⟨by simpa [← hW.2.2.1] using hwW, hwNot⟩

private theorem theorem_13_18_supportedOn_typeP_AZeroSetFromP_of_betaSupport
    {G : Type u} [Group G] [Finite G]
    {Smax W W1 W2 P U : Subgroup G}
    {βS : Section1.ClassFunction Smax}
    (hW : section12InternalDirectProduct W1 W2 W)
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (hβsupp : Section1.supportedOn βS
      (subgroupSetPreimage Smax (theorem_13_18_betaSupportSet Smax W W1 W2 P))) :
    Section1.supportedOn βS
      (subgroupSetPreimage Smax
        (theorem_13_18_typeP_AZeroSetFromP Smax W1 W2 P)) := by
  rw [Section1.supportedOn_iff] at hβsupp ⊢
  intro x hx
  exact hβsupp x
    (by
      intro hxβ
      exact hx (theorem_13_18_betaSupport_subset_typeP_AZeroSetFromP hW hTypeP
        (by simpa [subgroupSetPreimage] using hxβ)))

public theorem hypothesis_13_1_betaSupportNormDataFor_of_sourceData
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    hypothesis_13_1_betaSupportNormDataFor Smax Tmax W W1 W2 P Q p q u v := by
  have hsourceFull := hsource
  have hsourceSwap := section13_hypothesis_13_1_sourceData_swap hsourceFull
  have hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q :=
    section13_theorem_13_2_caseBData_bg_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceFull
  have hSTypeP : Section8.typePData Smax P U W1 W2 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceFull
  have hTTypeP : Section8.typePData Tmax Q V W2 W1 :=
    section13_theorem_13_2_case_9_7_hypothesis92TypePData_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c hsourceSwap
  have hc_one : c = 1 :=
    theorem_13_12 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceFull
  have hd_one : d = 1 :=
    theorem_13_12 Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c hsourceSwap
  rcases hsource with
    ⟨_hcaseSource, _hSTypePSource, _hTTypePSource, hp_card, hq_card, hC, hD,
      hc_card, hd_card, hU_card, hV_card, hSnonker, hTnonker, hDadeS,
      hDadeT, _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex,
      _hConjBetaTau, _hChoice, hMin, hFourSixS, hFourSixT⟩
  have hCbot : C = ⊥ :=
    (Subgroup.card_eq_one (H := C)).1 (hc_card.symm.trans hc_one)
  have hDbot : D = ⊥ :=
    (Subgroup.card_eq_one (H := D)).1 (hd_card.symm.trans hd_one)
  have hSCentralizerBot : subgroupCentralizerIn U P = ⊥ := hC.symm.trans hCbot
  have hTCentralizerBot : subgroupCentralizerIn V Q = ⊥ := hD.symm.trans hDbot
  have hBetaCards := hypothesis_13_1_betaSupportNormDataFor_source
    hMin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
    hDadeS hDadeT hFourSixS hFourSixT hSCentralizerBot hTCentralizerBot
    C D u v c d hC hD hU_card hV_card hc_card hd_card
  simpa [hp_card, hq_card] using hBetaCards

private theorem theorem_13_18_beta_pvs_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          Section1.supportedOn βS
            (subgroupSetPreimage Smax
              (theorem_13_18_betaSupportSet Smax W W1 W2 P)) := by
  intro hsource hnotation hβhyp
  rcases hβhyp with ⟨hj0, hjp, hβdef⟩
  have hBetaSupportNorm := hypothesis_13_1_betaSupportNormDataFor_of_sourceData
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource
  exact (hBetaSupportNorm.1 ω η μ ν μsum νsum δ δ' σ βS j
    hnotation hj0 hjp hβdef).1

private theorem theorem_13_18_beta_AZero_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Section1.supportedOn βS
        (subgroupSetPreimage Smax
          (theorem_13_18_betaSupportSet Smax W W1 W2 P)) →
        Section1.supportedOn βS
          (subgroupSetPreimage Smax (typePFAZeroSet Smax W1 W2 P)) := by
  intro hsource hβsupp
  rcases hsource with ⟨hcase, hSTypeP, _htail⟩
  have hβPF :
      Section1.supportedOn βS
        (subgroupSetPreimage Smax
          (theorem_13_18_typeP_AZeroSetFromP Smax W1 W2 P)) :=
    theorem_13_18_supportedOn_typeP_AZeroSetFromP_of_betaSupport
      hcase.1 hSTypeP hβsupp
  simpa [theorem_13_18_typeP_AZeroSetFromP] using hβPF

private theorem theorem_13_18_beta_norm_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          Section5.cfNormSq βS = ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 2 := by
  intro hsource hnotation hβhyp
  rcases hβhyp with ⟨hj0, hjp, hβdef⟩
  have hBetaSupportNorm := hypothesis_13_1_betaSupportNormDataFor_of_sourceData
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource
  exact (hBetaSupportNorm.1 ω η μ ν μsum νsum δ δ' σ βS j
    hnotation hj0 hjp hβdef).2

private theorem theorem_13_18_typeP_AZero_dade_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
  (p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      ∃ A0book : Set G, ∃ R : G → Subgroup G,
        ∃ hA0MG : Section2.Hypothesis2 A0book Smax R,
          typePFAZeroSet Smax W1 W2 P ⊆ A0book ∧
            ∀ χ : Section1.ClassFunction Smax,
              τS χ = Section2.dadeTransform R hA0MG.subset_L χ := by
  intro hsource
  exact theorem_13_2_typePFAZero_dadePackage
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource

private theorem theorem_13_18_typeP_AZero_agreesWithInduction_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      ∀ χ : Section1.ClassFunction Smax,
        Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) χ →
          τS χ = Section1.inducedCFLinear Smax χ := by
  intro hsource
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨_hMF, _hType, _hTypeII, _hUcomm, _hFrob, _hPelem, _hPcard, _huBound,
      _hCoh, _hTI, hTau, _hNormU⟩
  exact hTau.2

private theorem theorem_13_18_beta_support_norm_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          Section1.supportedOn βS
              (subgroupSetPreimage Smax
                ((section16NonidentityElements (P : Set G)) ∪
                  section16ConjugatesOfSetBySet
                    ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))
                    (Smax : Set G))) ∧
            Section1.supportedOn βS
              (subgroupSetPreimage Smax (typePFAZeroSet Smax W1 W2 P)) ∧
            Section5.cfNormSq βS = ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 2 := by
  intro hsource hnotation hβhyp
  have hβsuppNamed :
      Section1.supportedOn βS
        (subgroupSetPreimage Smax
          (theorem_13_18_betaSupportSet Smax W W1 W2 P)) :=
    theorem_13_18_beta_pvs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS j p q u v c d
      hsource hnotation hβhyp
  have hβsupp :
      Section1.supportedOn βS
        (subgroupSetPreimage Smax
          ((section16NonidentityElements (P : Set G)) ∪
            section16ConjugatesOfSetBySet
              ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))
              (Smax : Set G))) := by
    simpa [theorem_13_18_betaSupportSet] using hβsuppNamed
  have hβA0 :
      Section1.supportedOn βS
        (subgroupSetPreimage Smax (typePFAZeroSet Smax W1 W2 P)) :=
    theorem_13_18_beta_AZero_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT βS
      p q u v c d hsource hβsuppNamed
  have hβnorm :
      Section5.cfNormSq βS = ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 2 :=
    theorem_13_18_beta_norm_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS j p q u v c d
      hsource hnotation hβhyp
  exact ⟨hβsupp, hβA0, hβnorm⟩

private theorem theorem_13_18_beta_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          theorem_13_18_betaData Smax W W1 W2 P βS q u := by
  intro hsource hnotation hβhyp
  rcases theorem_13_18_beta_support_norm_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS j p q u v c d
      hsource hnotation hβhyp with
    ⟨hβsupp, hβA0, hβnorm⟩
  exact ⟨hβsupp, hβA0, hβnorm⟩

private theorem theorem_13_18_beta_CFOn_of_AZero
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P : Subgroup G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q : ℕ) :
    hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
      theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
        Section1.supportedOn βS
            (subgroupSetPreimage Smax (typePFAZeroSet Smax W1 W2 P)) →
          Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) βS := by
  intro hnotation hβhyp hβA0
  refine ⟨?_, ?_⟩
  · exact theorem_13_18_beta_isClassFunction_of_notation
      Smax Tmax W W1 W2 P p q ω η μ ν μsum νsum δ δ' σ βS j
      hnotation hβhyp
  · intro l hl
    exact (Section1.supportedOn_iff.mp hβA0) l
      (by simpa [subgroupSetPreimage] using hl)

private theorem theorem_13_18_beta_virtual_of_notation
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P : Subgroup G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q : ℕ) :
    hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
      theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
        Theory.Character.IsVirtualCharacter βS := by
  intro hnotation hβhyp
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', hμirr, _hνirr, _hμzero_nonprincipal,
      _hνzero_nonprincipal, _hμind, _hνind, _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  rcases hβhyp with ⟨_hj0, hjp, hβdef⟩
  have hindVirt :
      Theory.Character.IsVirtualCharacter
        (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) :=
    Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      ((P ⊔ W1).subgroupOf Smax)
      (Section3.isVirtualCharacter_principalCharacter
        (G := ((P ⊔ W1).subgroupOf Smax)))
  have hμvirt : Theory.Character.IsVirtualCharacter (μ 0 j) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hμirr 0 j hqpos hjp)
  rw [hβdef]
  exact Section3.isVirtualCharacter_sub hindVirt hμvirt

private theorem theorem_13_18_beta_tau_cfNormSq_eq
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) βS →
        βτ = τS βS →
          Section5.cfNormSq βτ = Section5.cfNormSq βS := by
  intro hsource hβCFOn hβτ
  rcases theorem_13_18_typeP_AZero_dade_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource with
    ⟨A0book, R, hA0MG, hA0sub, hτDade⟩
  have hβCFOnBook : Section2.CFOn Smax A0book βS := by
    refine ⟨hβCFOn.1, ?_⟩
    intro l hl
    exact hβCFOn.2 l (fun hlTypeP => hl (hA0sub hlTypeP))
  have hτβ : τS βS =
      Section2.dadeTransform R hA0MG.subset_L βS :=
    hτDade βS
  unfold Section5.cfNormSq
  rw [hβτ, hτβ]
  exact congrArg Complex.re
    ((Section2.theorem_2_6 A0book Smax R hA0MG hA0MG.subset_L).1
      βS βS hβCFOnBook hβCFOnBook)

private theorem theorem_13_18_beta_tau_virtual_of_AZero
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) βS →
            βτ = τS βS →
              Theory.Character.IsVirtualCharacter βτ := by
  intro hsource hnotation hβhyp hβCFOn hβτ
  rcases theorem_13_18_typeP_AZero_dade_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource with
    ⟨A0book, R, hA0MG, hA0sub, hτDade⟩
  have hβvirt : Theory.Character.IsVirtualCharacter βS :=
    theorem_13_18_beta_virtual_of_notation
      Smax Tmax W W1 W2 P ω η μ ν μsum νsum δ δ' σ βS j p q
      hnotation hβhyp
  have hβCFOnBook : Section2.CFOn Smax A0book βS := by
    refine ⟨hβCFOn.1, ?_⟩
    intro l hl
    exact hβCFOn.2 l (fun hlTypeP => hl (hA0sub hlTypeP))
  have hβvirtOn : Section2.virtualCharacterOn Smax A0book βS :=
    ⟨hβvirt, hβCFOnBook.2⟩
  have hτβ : τS βS =
      Section2.dadeTransform R hA0MG.subset_L βS :=
    hτDade βS
  rw [hβτ, hτβ]
  exact (Section2.theorem_2_6 A0book Smax R hA0MG hA0MG.subset_L).2
    βS hβvirtOn

private theorem theorem_13_18_decomposition_X_eta_coeff_integer
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ X Y : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          Section1.supportedOn βS
            (subgroupSetPreimage Smax (typePFAZeroSet Smax W1 W2 P)) →
            βτ = τS βS →
              Γ = βτ - Section1.principalCharacter G + η 0 j →
                Γ = X + Y →
                  theorem_13_18_decompositionData p q η X Y →
                    ∃ a : ℤ, Section1.scalarProduct G X (η 0 j) = (a : ℂ) := by
  intro hsource hnotation hβhyp hβA0 hβτ hΓ hΓXY hdecomp
  have hnotationFull := hnotation
  have hβhypFull := hβhyp
  rcases hβhyp with ⟨_hj0, hjp, _hβdef⟩
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  have hβCFOn : Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) βS :=
    theorem_13_18_beta_CFOn_of_AZero
      Smax Tmax W W1 W2 P ω η μ ν μsum νsum δ δ' σ βS j p q
      hnotationFull hβhypFull hβA0
  have hβτvirt : Theory.Character.IsVirtualCharacter βτ :=
    theorem_13_18_beta_tau_virtual_of_AZero
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ j p q u v c d
      hsource hnotationFull hβhypFull hβCFOn hβτ
  have hprincipalVirt :
      Theory.Character.IsVirtualCharacter (Section1.principalCharacter G) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := G))
  have hηvirt : Theory.Character.IsVirtualCharacter (η 0 j) :=
    theorem_13_18_eta_virtual_of_notation Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ hnotationFull 0 j hqpos hjp
  have hΓvirt : Theory.Character.IsVirtualCharacter Γ := by
    rw [hΓ]
    exact Section3.isVirtualCharacter_add
      (Section3.isVirtualCharacter_sub hβτvirt hprincipalVirt) hηvirt
  have hYηj : Section1.scalarProduct G Y (η 0 j) = 0 :=
    hdecomp.2 0 j hqpos hjp
  have hΓηj :
      Section1.scalarProduct G Γ (η 0 j) =
        Section1.scalarProduct G X (η 0 j) := by
    rw [hΓXY, Section1.scalarProduct_add_left, hYηj]
    simp
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hΓvirt hηvirt with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [← hΓηj]
  exact ha

private theorem theorem_13_18_decomposition_X_conjugate_eta_coeff
    {G : Type u}
    [Group G]
    [Finite G]
    {p q : ℕ}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {Γ X Y : Section1.ClassFunction G}
    {j k : ℕ} {a : ℤ}
    (hΓreal : Γ = Section1.conjugateCharacter Γ)
    (hΓXY : Γ = X + Y)
    (hdecomp : theorem_13_18_decompositionData p q η X Y)
    (hqpos : 0 < q)
    (hjp : j < p)
    (hkp : k < p)
    (hηk : η 0 k = Section1.conjugateCharacter (η 0 j))
    (hXηj : Section1.scalarProduct G X (η 0 j) = (a : ℂ)) :
    Section1.scalarProduct G X (η 0 k) = (a : ℂ) := by
  have hYηj : Section1.scalarProduct G Y (η 0 j) = 0 :=
    hdecomp.2 0 j hqpos hjp
  have hYηk : Section1.scalarProduct G Y (η 0 k) = 0 :=
    hdecomp.2 0 k hqpos hkp
  have hΓηj :
      Section1.scalarProduct G Γ (η 0 j) =
        Section1.scalarProduct G X (η 0 j) := by
    rw [hΓXY, Section1.scalarProduct_add_left, hYηj]
    simp
  have hΓηk :
      Section1.scalarProduct G Γ (η 0 k) =
        Section1.scalarProduct G X (η 0 k) := by
    rw [hΓXY, Section1.scalarProduct_add_left, hYηk]
    simp
  have hconj :
      Section1.scalarProduct G Γ (η 0 k) =
        star (Section1.scalarProduct G Γ (η 0 j)) := by
    calc
      Section1.scalarProduct G Γ (η 0 k)
          = Section1.scalarProduct G (Section1.conjugateCharacter Γ)
              (Section1.conjugateCharacter (η 0 j)) := by
            rw [hηk]
            exact congrArg
              (fun t => Section1.scalarProduct G t (Section1.conjugateCharacter (η 0 j)))
              hΓreal
      _ = star (Section1.scalarProduct G Γ
              (Section1.conjugateCharacter (Section1.conjugateCharacter (η 0 j)))) :=
            theorem_13_18_scalarProduct_conjugate_left Γ
              (Section1.conjugateCharacter (η 0 j))
      _ = star (Section1.scalarProduct G Γ (η 0 j)) := by
            rw [theorem_13_18_conjugateCharacter_involutive]
  have hΓηj_int : Section1.scalarProduct G Γ (η 0 j) = (a : ℂ) := by
    rw [hΓηj, hXηj]
  have hΓηk_int : Section1.scalarProduct G Γ (η 0 k) = (a : ℂ) := by
    rw [hconj, hΓηj_int]
    simp
  rw [← hΓηk]
  exact hΓηk_int

private theorem theorem_13_18_tau_mu_zero_row_difference_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          ∀ k : ℕ, 0 < k → k < p →
            τS (μ 0 k - μ 0 j) = η 0 k - η 0 j := by
  intro hsource hnotation hβhyp
  have hsourceFull := hsource
  have hnotationFull := hnotation
  rcases hβhyp with ⟨hj0, hjp, _hβdef⟩
  rcases hnotation with
    ⟨hωData, _hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, hDadeDiff, hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin⟩
  have hsign :
      theorem_13_3_signNormalizationFor p q δ δ' :=
    ((theorem_13_3 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceFull).1
      ω η μ ν μsum νsum δ δ' σ hnotationFull).1
  intro k hk0 hkp
  have hdeg :
      Section1.degree (μ 0 k) = Section1.degree (μ 0 j) :=
    (hZeroDegree ω η μ ν μsum νsum δ δ' σ hnotationFull).1
      k j hk0 hkp hj0 hjp
  have hdiff :
      τS (μ 0 k - μ 0 j) =
        (((δ k : ℤ) : ℂ) • (σ (ω 0 k) - σ (ω 0 j))) :=
    (hDadeDiff ω η μ ν μsum νsum δ δ' σ hnotationFull).1
      0 k j hqpos hk0 hkp hj0 hjp hdeg
  have hδk : δ k = 1 := hsign.1 k hkp
  have hηk : η 0 k = σ (ω 0 k) := hη 0 k hqpos hkp
  have hηj : η 0 j = σ (ω 0 j) := hη 0 j hqpos hjp
  calc
    τS (μ 0 k - μ 0 j)
        = (((δ k : ℤ) : ℂ) • (σ (ω 0 k) - σ (ω 0 j))) := hdiff
    _ = η 0 k - η 0 j := by
          rw [hδk]
          simp [hηk, hηj]

private theorem theorem_13_18_gamma_independence_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            Γ = βτ - Section1.principalCharacter G + η 0 j →
              ∀ k : ℕ, 0 < k → k < p →
                Γ =
                  τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                    (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                      μ 0 k) - Section1.principalCharacter G + η 0 k := by
  intro hsource hnotation hβhyp hβτ hΓ k hk0 hkp
  rcases hβhyp with ⟨hj0, hjp, hβdef⟩
  let H : Subgroup Smax := (P ⊔ W1).subgroupOf Smax
  let I : Section1.ClassFunction Smax :=
    Section1.inducedCF H (Section1.principalCharacter H)
  have hβτ_expand : βτ = τS (I - μ 0 j) := by
    rw [hβτ, hβdef]
  have hdiff :
      τS (μ 0 k - μ 0 j) = η 0 k - η 0 j :=
    theorem_13_18_tau_mu_zero_row_difference_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS j p q u v c d
      hsource hnotation ⟨hj0, hjp, hβdef⟩ k hk0 hkp
  have hlinear :
      τS (I - μ 0 j) = τS (I - μ 0 k) + τS (μ 0 k - μ 0 j) := by
    calc
      τS (I - μ 0 j)
          = τS ((I - μ 0 k) + (μ 0 k - μ 0 j)) := by
            congr 1
            ext x
            simp [Pi.sub_apply, Pi.add_apply]
      _ = τS (I - μ 0 k) + τS (μ 0 k - μ 0 j) := by
            rw [map_add]
  rw [hΓ, hβτ_expand]
  calc
    τS (I - μ 0 j) - Section1.principalCharacter G + η 0 j
        = (τS (I - μ 0 k) + τS (μ 0 k - μ 0 j)) -
            Section1.principalCharacter G + η 0 j := by
          rw [hlinear]
    _ = (τS (I - μ 0 k) + (η 0 k - η 0 j)) -
            Section1.principalCharacter G + η 0 j := by
          rw [hdiff]
    _ = τS (I - μ 0 k) - Section1.principalCharacter G + η 0 k := by
          ext x
          simp [Pi.sub_apply, Pi.add_apply, Section1.principalCharacter]
          ring

private theorem theorem_13_18_mu_zero_row_nonprincipal_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          μ 0 j ≠ Section1.principalCharacter Smax := by
  intro _hsource hnotation hβhyp
  rcases hβhyp with ⟨hj0, hjp, _hβdef⟩
  rcases hnotation with
    ⟨_hωData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
      hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  exact hμzero_nonprincipal j hj0 hjp

private theorem theorem_13_18_mu_zero_row_principal_orthogonal_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          Section1.scalarProduct Smax (μ 0 j) (Section1.principalCharacter Smax) = 0 := by
  intro hsource hnotation hβhyp
  have hnotationFull := hnotation
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  rcases hβhyp with ⟨hj0, hjp, hβdef⟩
  have hμ_nonprincipal : μ 0 j ≠ Section1.principalCharacter Smax :=
    theorem_13_18_mu_zero_row_nonprincipal_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS j p q u v c d
      hsource hnotationFull ⟨hj0, hjp, hβdef⟩
  exact theorem_13_18_irreducible_nonprincipal_principal_orthogonal
    (hμirr 0 j hqpos hjp) hμ_nonprincipal

private theorem theorem_13_18_beta_principal_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          Section1.scalarProduct Smax βS (Section1.principalCharacter Smax) = 1 := by
  intro hsource hnotation hβhyp
  rcases hβhyp with ⟨_hj0, _hjp, hβdef⟩
  let H : Subgroup Smax := (P ⊔ W1).subgroupOf Smax
  have hres :
      Section1.subgroupRestriction H (Section1.principalCharacter Smax) =
        Section1.principalCharacter H := by
    ext x
    rfl
  have hIndOne :
      Section1.scalarProduct Smax
          (Section1.inducedCF H (Section1.principalCharacter H))
          (Section1.principalCharacter Smax) = 1 := by
    calc
      Section1.scalarProduct Smax
          (Section1.inducedCF H (Section1.principalCharacter H))
          (Section1.principalCharacter Smax)
          = Section1.scalarProduct H (Section1.principalCharacter H)
              (Section1.subgroupRestriction H (Section1.principalCharacter Smax)) :=
            Section1.scalarProduct_inducedCF_left H
              (Section1.principalCharacter H) (Section1.principalCharacter Smax)
              (by intro x g; simp [Section1.principalCharacter])
      _ = Section1.scalarProduct H (Section1.principalCharacter H)
              (Section1.principalCharacter H) := by
            rw [hres]
      _ = 1 := theorem_13_18_scalarProduct_principalCharacter_self
  have hμ_one :
      Section1.scalarProduct Smax (μ 0 j) (Section1.principalCharacter Smax) = 0 :=
    theorem_13_18_mu_zero_row_principal_orthogonal_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS j p q u v c d
      hsource hnotation ⟨_hj0, _hjp, hβdef⟩
  calc
    Section1.scalarProduct Smax βS (Section1.principalCharacter Smax)
        = Section1.scalarProduct Smax
            (Section1.inducedCF H (Section1.principalCharacter H) - μ 0 j)
            (Section1.principalCharacter Smax) := by
          rw [hβdef]
    _ = Section1.scalarProduct Smax
            (Section1.inducedCF H (Section1.principalCharacter H))
            (Section1.principalCharacter Smax) -
          Section1.scalarProduct Smax (μ 0 j)
            (Section1.principalCharacter Smax) := by
          rw [theorem_13_18_scalarProduct_sub_left]
    _ = 1 := by
          simp [hIndOne, hμ_one]

private theorem theorem_13_18_beta_tau_principal_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            Section1.scalarProduct G βτ (Section1.principalCharacter G) = 1 := by
  intro hsource hnotation hβhyp hβτ
  have hβdata :
      theorem_13_18_betaData Smax W W1 W2 P βS q u :=
    theorem_13_18_beta_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS j p q u v c d
      hsource hnotation hβhyp
  rcases hβdata with ⟨_hβsupp, hβA0, _hβnorm⟩
  have hβclass : Section1.IsClassFunction βS :=
    theorem_13_18_beta_isClassFunction_of_notation
      Smax Tmax W W1 W2 P p q ω η μ ν μsum νsum δ δ' σ βS j
      hnotation hβhyp
  have hβCFOn : Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) βS := by
    refine ⟨hβclass, ?_⟩
    intro l hl
    exact (Section1.supportedOn_iff.mp hβA0) l
      (by simpa [subgroupSetPreimage] using hl)
  have hTau :=
    theorem_13_18_typeP_AZero_agreesWithInduction_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
  have hτβ : τS βS = Section1.inducedCFLinear Smax βS :=
    hTau βS hβCFOn
  have hres :
      Section1.subgroupRestriction Smax (Section1.principalCharacter G) =
        Section1.principalCharacter Smax := by
    ext x
    rfl
  have hβ_principal :
      Section1.scalarProduct Smax βS (Section1.principalCharacter Smax) = 1 :=
    theorem_13_18_beta_principal_source_bridge
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ βS j p q u v c d
        hsource hnotation hβhyp
  calc
    Section1.scalarProduct G βτ (Section1.principalCharacter G)
        = Section1.scalarProduct G (τS βS) (Section1.principalCharacter G) := by
          rw [hβτ]
    _ = Section1.scalarProduct G (Section1.inducedCF Smax βS)
          (Section1.principalCharacter G) := by
          rw [hτβ, Section1.inducedCFLinear_apply]
    _ = Section1.scalarProduct Smax βS
          (Section1.subgroupRestriction Smax (Section1.principalCharacter G)) :=
          Section1.scalarProduct_inducedCF_left Smax βS
            (Section1.principalCharacter G)
            (by intro x g; simp [Section1.principalCharacter])
    _ = Section1.scalarProduct Smax βS (Section1.principalCharacter Smax) := by
          rw [hres]
    _ = 1 := hβ_principal

private theorem theorem_13_18_conjugate_beta_tau_index_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            Γ = βτ - Section1.principalCharacter G + η 0 j →
                ∃ k : ℕ, 0 < k ∧ k < p ∧ k ≠ j ∧
                    η 0 k = Section1.conjugateCharacter (η 0 j) ∧
                      Section1.conjugateCharacter βτ =
                        τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                            μ 0 k) := by
  intro hsource hnotation hβhyp hβτ _hΓ
  rcases hβhyp with ⟨hj0, hjp, hβdef⟩
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, hConjIndex, hConjBetaTau,
      _hChoice, _hMin⟩
  rcases (hConjIndex ω η μ ν μsum νsum δ δ' σ hnotation).1
      j hj0 hjp with
    ⟨k, hk0, hkp, hkj, hηk, hμk⟩
  refine ⟨k, hk0, hkp, hkj, hηk, ?_⟩
  rw [hβτ, hβdef]
  exact (hConjBetaTau ω η μ ν μsum νsum δ δ' σ hnotation).1
    j k hj0 hjp hk0 hkp hμk

private theorem theorem_13_18_conjugate_gamma_index_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            Γ = βτ - Section1.principalCharacter G + η 0 j →
              ∃ k : ℕ, 0 < k ∧ k < p ∧ k ≠ j ∧
                  η 0 k = Section1.conjugateCharacter (η 0 j) ∧
                    Section1.conjugateCharacter Γ =
                      τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                          μ 0 k) - Section1.principalCharacter G + η 0 k := by
  intro hsource hnotation hβhyp hβτ hΓ
  rcases theorem_13_18_conjugate_beta_tau_index_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ j p q u v c d
      hsource hnotation hβhyp hβτ hΓ with
    ⟨k, hk0, hkp, hkj, hηk, hβτconj⟩
  refine ⟨k, hk0, hkp, hkj, hηk, ?_⟩
  calc
    Section1.conjugateCharacter Γ
        = Section1.conjugateCharacter
            (βτ - Section1.principalCharacter G + η 0 j) := by
          rw [hΓ]
    _ = Section1.conjugateCharacter βτ -
          Section1.principalCharacter G + Section1.conjugateCharacter (η 0 j) := by
          ext x
          simp [Section1.conjugateCharacter, Section1.principalCharacter,
            Pi.sub_apply, Pi.add_apply]
    _ = τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
            μ 0 k) - Section1.principalCharacter G + η 0 k := by
          rw [hβτconj, ← hηk]

private theorem theorem_13_18_gamma_real_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            Γ = βτ - Section1.principalCharacter G + η 0 j →
              Γ = Section1.conjugateCharacter Γ := by
  intro hsource hnotation hβhyp hβτ hΓ
  rcases theorem_13_18_conjugate_gamma_index_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ j p q u v c d
      hsource hnotation hβhyp hβτ hΓ with
    ⟨k, hk0, hkp, _hkne, _hηk, hconjΓ⟩
  have hΓk :
      Γ =
        τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
            μ 0 k) - Section1.principalCharacter G + η 0 k :=
    theorem_13_18_gamma_independence_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ j p q u v c d
      hsource hnotation hβhyp hβτ hΓ k hk0 hkp
  exact hΓk.trans hconjΓ.symm

private theorem theorem_13_18_gamma_facts_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            Γ = βτ - Section1.principalCharacter G + η 0 j →
              (∀ k : ℕ, 0 < k → k < p →
                Γ =
                  τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                    (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                      μ 0 k) - Section1.principalCharacter G + η 0 k) ∧
              Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0 ∧
              Γ = Section1.conjugateCharacter Γ := by
  intro hsource hnotation hβhyp hβτ hΓ
  rcases hβhyp with ⟨hj0, hjp, hβdef⟩
  have hβhyp : theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p :=
    ⟨hj0, hjp, hβdef⟩
  have hΓindep :
      ∀ k : ℕ, 0 < k → k < p →
        Γ =
          τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
              μ 0 k) - Section1.principalCharacter G + η 0 k :=
    theorem_13_18_gamma_independence_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ j p q u v c d
      hsource hnotation hβhyp hβτ hΓ
  have hβτ_one :
      Section1.scalarProduct G βτ (Section1.principalCharacter G) = 1 :=
    theorem_13_18_beta_tau_principal_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ j p q u v c d
      hsource hnotation hβhyp hβτ
  have hη_one :
      Section1.scalarProduct G (η 0 j) (Section1.principalCharacter G) = 0 :=
    theorem_13_18_eta_zero_row_principal_orthogonal_of_notation
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ
      hnotation j hj0 hjp
  have hΓ_one :
      Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0 := by
    rw [hΓ]
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left]
    rw [hβτ_one, theorem_13_18_scalarProduct_principalCharacter_self, hη_one]
    ring
  have hΓ_real : Γ = Section1.conjugateCharacter Γ :=
    theorem_13_18_gamma_real_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ j p q u v c d
      hsource hnotation hβhyp hβτ hΓ
  exact ⟨hΓindep, hΓ_one, hΓ_real⟩

private theorem theorem_13_18_gamma_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            Γ = βτ - Section1.principalCharacter G + η 0 j →
              theorem_13_18_gammaData Smax P W1 τS η Γ p := by
  intro hsource hnotation hβhyp hβτ hΓ
  rcases theorem_13_18_gamma_facts_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ j p q u v c d
      hsource hnotation hβhyp hβτ hΓ with
    ⟨hΓindep, hΓone, hΓreal⟩
  refine ⟨?_, hΓone, hΓreal⟩
  intro k hk0 hkp
  let βSk : Section1.ClassFunction Smax :=
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ 0 k
  let βτk : Section1.ClassFunction G := τS βSk
  refine ⟨μ 0 k, βSk, βτk, ?_, rfl, ?_⟩
  · exact ⟨hk0, hkp, rfl⟩
  · exact hΓindep k hk0 hkp

private theorem theorem_13_18_decomposition_norm_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ X Y : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            Γ = βτ - Section1.principalCharacter G + η 0 j →
              theorem_13_18_betaData Smax W W1 W2 P βS q u →
                theorem_13_18_gammaData Smax P W1 τS η Γ p →
                  Γ = X + Y →
                    theorem_13_18_decompositionData p q η X Y →
                      Section5.cfNormSq Y ≤ ((u - 1 : ℕ) : ℝ) / (q : ℝ) := by
  intro hsource hnotation hβhyp hβτ hΓ hβdata hΓdata hΓXY hdecomp
  classical
  have hnotationFull := hnotation
  have hβhypFull := hβhyp
  rcases hβhyp with ⟨hj0, hjp, _hβdef⟩
  rcases hβdata with ⟨_hβsupp, hβA0, hβnorm⟩
  rcases hΓdata with ⟨_hΓindep, hΓone, hΓreal⟩
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, hppos, _ωFin, _hωFin, _hωNat⟩
  have hβCFOn : Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) βS :=
    theorem_13_18_beta_CFOn_of_AZero
      Smax Tmax W W1 W2 P ω η μ ν μsum νsum δ δ' σ βS j p q
      hnotationFull hβhypFull hβA0
  have hβτnorm_eq : Section5.cfNormSq βτ = Section5.cfNormSq βS :=
    theorem_13_18_beta_tau_cfNormSq_eq
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT βS βτ
      p q u v c d hsource hβCFOn hβτ
  have hβτnorm :
      Section5.cfNormSq βτ = ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 2 := by
    rw [hβτnorm_eq, hβnorm]
  let B : Section1.ClassFunction G := Section1.principalCharacter G - η 0 j + X
  have hβτ_of_Γ : βτ = Γ + Section1.principalCharacter G - η 0 j := by
    rw [hΓ]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
    ring
  have hβτ_decomp : βτ = B + Y := by
    rw [hβτ_of_Γ, hΓXY]
    ext g
    simp [B, Pi.sub_apply, Pi.add_apply]
    ring
  have hη00 : η 0 0 = Section1.principalCharacter G :=
    theorem_13_18_eta_zero_zero_eq_principal_of_notation
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ hnotationFull
  have hYη00 : Section1.scalarProduct G Y (η 0 0) = 0 :=
    hdecomp.2 0 0 hqpos hppos
  have hYone : Section1.scalarProduct G Y (Section1.principalCharacter G) = 0 := by
    simpa [hη00] using hYη00
  have hYηj : Section1.scalarProduct G Y (η 0 j) = 0 :=
    hdecomp.2 0 j hqpos hjp
  have hYX : Section1.scalarProduct G Y X = 0 :=
    theorem_13_18_decomposition_scalarProduct_Y_X_eq_zero hdecomp
  have hYB : Section1.scalarProduct G Y B = 0 := by
    dsimp [B]
    rw [Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right,
      hYone, hYηj, hYX]
    ring
  have hBY : Section1.scalarProduct G B Y = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hYB
  have hβτ_norm_split :
      Section5.cfNormSq βτ = Section5.cfNormSq B + Section5.cfNormSq Y := by
    rw [hβτ_decomp]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hBY hYB
  rcases theorem_13_18_conjugate_gamma_index_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ j p q u v c d
      hsource hnotationFull hβhypFull hβτ hΓ with
    ⟨k, hk0, hkp, hkne, hηk, _hconjΓ⟩
  rcases theorem_13_18_decomposition_X_eta_coeff_integer
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ X Y j p q u v c d
      hsource hnotationFull hβhypFull hβA0 hβτ hΓ hΓXY hdecomp with
    ⟨a, hXηj⟩
  have hXηk : Section1.scalarProduct G X (η 0 k) = (a : ℂ) :=
    theorem_13_18_decomposition_X_conjugate_eta_coeff
      hΓreal hΓXY hdecomp hqpos hjp hkp hηk hXηj
  have hηorth :
      ∀ i k i' k' : ℕ, i < q → k < p → i' < q → k' < p →
        Section1.scalarProduct G (η i k) (η i' k') =
          if i = i' ∧ k = k' then 1 else 0 :=
    theorem_13_18_eta_orthonormal_of_notation
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ hnotationFull
  have hηj_self : Section1.scalarProduct G (η 0 j) (η 0 j) = 1 := by
    simpa using hηorth 0 j 0 j hqpos hjp hqpos hjp
  have hηk_self : Section1.scalarProduct G (η 0 k) (η 0 k) = 1 := by
    simpa using hηorth 0 k 0 k hqpos hkp hqpos hkp
  have hηj_one : Section1.scalarProduct G (η 0 j) (Section1.principalCharacter G) = 0 :=
    theorem_13_18_eta_zero_row_principal_orthogonal_of_notation
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ hnotationFull j hj0 hjp
  have hηk_one : Section1.scalarProduct G (η 0 k) (Section1.principalCharacter G) = 0 :=
    theorem_13_18_eta_zero_row_principal_orthogonal_of_notation
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ hnotationFull k hk0 hkp
  have hone_ηj : Section1.scalarProduct G (Section1.principalCharacter G) (η 0 j) = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hηj_one
  have hone_ηk : Section1.scalarProduct G (Section1.principalCharacter G) (η 0 k) = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hηk_one
  have hηjηk : Section1.scalarProduct G (η 0 j) (η 0 k) = 0 := by
    have hjne : j ≠ k := fun h => hkne h.symm
    simpa [hjne] using hηorth 0 j 0 k hqpos hjp hqpos hkp
  have hηkηj : Section1.scalarProduct G (η 0 k) (η 0 j) = 0 := by
    simpa [hkne] using hηorth 0 k 0 j hqpos hkp hqpos hjp
  have hXone : Section1.scalarProduct G X (Section1.principalCharacter G) = 0 := by
    rw [hΓXY, Section1.scalarProduct_add_left, hYone] at hΓone
    simpa using hΓone
  have hB_one : Section1.scalarProduct G B (Section1.principalCharacter G) = 1 := by
    dsimp [B]
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
      theorem_13_18_scalarProduct_principalCharacter_self, hηj_one, hXone]
    ring
  have hB_ηj : Section1.scalarProduct G B (η 0 j) = (a : ℂ) - 1 := by
    dsimp [B]
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
      hone_ηj, hηj_self, hXηj]
    ring
  have hB_ηk : Section1.scalarProduct G B (η 0 k) = (a : ℂ) := by
    dsimp [B]
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
      hone_ηk, hηjηk, hXηk]
    ring
  have hB_lower : (2 : ℝ) ≤ Section5.cfNormSq B :=
    theorem_13_18_three_coeff_lower_bound
      (Section1.principalCharacter G) (η 0 j) (η 0 k) B a
      theorem_13_18_scalarProduct_principalCharacter_self hηj_self hηk_self
      hone_ηj hηj_one hone_ηk hηk_one hηjηk hηkηj
      hB_one hB_ηj hB_ηk
  have hsum :
      Section5.cfNormSq B + Section5.cfNormSq Y =
        ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 2 := by
    rw [← hβτ_norm_split, hβτnorm]
  nlinarith

private theorem theorem_13_18_decomposition_source_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ Γ : Section1.ClassFunction G)
    (j p q u v c d : ℕ) :
    hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            Γ = βτ - Section1.principalCharacter G + η 0 j →
              theorem_13_18_betaData Smax W W1 W2 P βS q u →
                theorem_13_18_gammaData Smax P W1 τS η Γ p →
                  ∃ X Y : Section1.ClassFunction G,
                    theorem_13_18_decompositionNormData p q u η Γ X Y := by
  intro hsource hnotation hβhyp hβτ hΓ hβdata hΓdata
  rcases theorem_13_18_projection_decomposition_of_notation
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ Γ hnotation with
    ⟨X, Y, hΓXY, hdecomp⟩
  have hYnorm : Section5.cfNormSq Y ≤ ((u - 1 : ℕ) : ℝ) / (q : ℝ) :=
    theorem_13_18_decomposition_norm_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ X Y j p q u v c d
      hsource hnotation hβhyp hβτ hΓ hβdata hΓdata hΓXY hdecomp
  exact ⟨X, Y, hΓXY, hdecomp, hYnorm⟩

public theorem theorem_13_18
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (βS : Section1.ClassFunction Smax)
    (βτ : Section1.ClassFunction G)
    (j p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        theorem_13_18_hypothesis Smax P W1 (μ 0 j) βS j p →
          βτ = τS βS →
            ∃ Γ X Y η0j : Section1.ClassFunction G,
              Section1.supportedOn βS
                  (subgroupSetPreimage Smax
                    ((section16NonidentityElements (P : Set G)) ∪
                      section16ConjugatesOfSetBySet
                        ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (Smax : Set G))) ∧
                Section1.supportedOn βS (subgroupSetPreimage Smax (typePFAZeroSet Smax W1 W2 P)) ∧
                Section5.cfNormSq βS = ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 2 ∧
                η0j = η 0 j ∧
                Γ = βτ - Section1.principalCharacter G + η0j ∧
                (∀ k : ℕ, 0 < k → k < p →
                  ∃ (μ0k βSk : Section1.ClassFunction Smax) (βτk : Section1.ClassFunction G),
                    theorem_13_18_hypothesis Smax P W1 μ0k βSk k p ∧
                      βτk = τS βSk ∧
                      Γ = βτk - Section1.principalCharacter G + η 0 k) ∧
                Section1.scalarProduct G Γ (Section1.principalCharacter G) = 0 ∧
                Γ = Section1.conjugateCharacter Γ ∧
                Theory.Character.IsVirtualCharacter Γ ∧
                Γ = X + Y ∧
                theorem_13_18_decompositionData p q η X Y ∧
                Section5.cfNormSq Y ≤ ((u - 1 : ℕ) : ℝ) / (q : ℝ) := by
  intro hsource hnotation hβhyp hβτ
  have hβdata :
      theorem_13_18_betaData Smax W W1 W2 P βS q u :=
    theorem_13_18_beta_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS j p q u v c d
      hsource hnotation hβhyp
  let η0j : Section1.ClassFunction G := η 0 j
  let Γ : Section1.ClassFunction G := βτ - Section1.principalCharacter G + η0j
  have hΓdef : Γ = βτ - Section1.principalCharacter G + η 0 j := by
    rfl
  have hΓdata :
      theorem_13_18_gammaData Smax P W1 τS η Γ p :=
    theorem_13_18_gamma_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ j p q u v c d
      hsource hnotation hβhyp hβτ hΓdef
  rcases theorem_13_18_decomposition_source_bridge
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ Γ j p q u v c d
      hsource hnotation hβhyp hβτ hΓdef hβdata hΓdata with
    ⟨X, Y, hdecompNorm⟩
  rcases hβdata with ⟨hβsupp, hβA0, hβnorm⟩
  rcases hΓdata with ⟨hΓindep, hΓone, hΓreal⟩
  rcases hdecompNorm with ⟨hΓXY, hdecomp, hYnorm⟩
  have hβhypFull := hβhyp
  have hnotationFull := hnotation
  rcases hβhyp with ⟨_hjpos, hjp, _hβdef⟩
  rcases hnotation with ⟨hωData, _hμData, _hνData, _hηeq, _hωeq, _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  have hβCFOn : Section2.CFOn Smax (typePFAZeroSet Smax W1 W2 P) βS :=
    theorem_13_18_beta_CFOn_of_AZero
      Smax Tmax W W1 W2 P ω η μ ν μsum νsum δ δ' σ βS j p q
      hnotationFull hβhypFull hβA0
  have hβτvirt : Theory.Character.IsVirtualCharacter βτ :=
    theorem_13_18_beta_tau_virtual_of_AZero
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ βS βτ j p q u v c d
      hsource hnotationFull hβhypFull hβCFOn hβτ
  have hprincipalVirt :
      Theory.Character.IsVirtualCharacter (Section1.principalCharacter G) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := G))
  have hηvirt : Theory.Character.IsVirtualCharacter η0j := by
    rw [show η0j = η 0 j by rfl]
    exact theorem_13_18_eta_virtual_of_notation Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ hnotationFull 0 j hqpos hjp
  have hΓvirt : Theory.Character.IsVirtualCharacter Γ := by
    rw [hΓdef]
    exact Section3.isVirtualCharacter_add
      (Section3.isVirtualCharacter_sub hβτvirt hprincipalVirt) hηvirt
  refine ⟨Γ, X, Y, η0j, hβsupp, hβA0, hβnorm, ?_, ?_, hΓindep,
    hΓone, hΓreal, hΓvirt, hΓXY, hdecomp, hYnorm⟩
  · rfl
  · rfl
end CFSG.Section13

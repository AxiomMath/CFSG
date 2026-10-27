module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H
open scoped commutatorElement Matrix

private abbrev s16h_H5O4aCoord : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private theorem s16h_H5O4a_quad_explicit {K : Type} [Field K] {b c : K}
    (v : s16h_H5O4aCoord → K) :
    StatedQuadMinus 2 K b c v =
      v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
        b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
        c * v (Sum.inr (Sum.inr 1)) ^ 2 := by
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]

private theorem s16h_H5O4a_quad_scale {K : Type} [Field K] {b c : K}
    (d : s16h_H5O4aCoord → K)
    (hd : d (Sum.inl 0) * d (Sum.inr (Sum.inl 0)) = 1)
    (hu : d (Sum.inr (Sum.inr 0)) = 1) (hv : d (Sum.inr (Sum.inr 1)) = 1)
    (v : s16h_H5O4aCoord → K) :
    StatedQuadMinus 2 K b c (fun i => d i * v i) = StatedQuadMinus 2 K b c v := by
  rw [s16h_H5O4a_quad_explicit, s16h_H5O4a_quad_explicit]
  rw [show (d (Sum.inl 0) * v (Sum.inl 0)) *
        (d (Sum.inr (Sum.inl 0)) * v (Sum.inr (Sum.inl 0))) =
        v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) from by
      rw [mul_mul_mul_comm, hd, one_mul]]
  rw [hu, hv]
  ring

private theorem s16h_H5O4a_quad_swap {K : Type} [Field K] {b c : K}
    (v : s16h_H5O4aCoord → K) :
    StatedQuadMinus 2 K b c
        (v ∘ Equiv.swap (Sum.inl 0 : s16h_H5O4aCoord) (Sum.inr (Sum.inl 0))) =
      StatedQuadMinus 2 K b c v := by
  have hu1 : (Sum.inr (Sum.inr (0 : Fin 2)) : s16h_H5O4aCoord) ≠ Sum.inl 0 := by decide
  have hu2 : (Sum.inr (Sum.inr (0 : Fin 2)) : s16h_H5O4aCoord) ≠
    Sum.inr (Sum.inl 0) := by decide
  have hv1 : (Sum.inr (Sum.inr (1 : Fin 2)) : s16h_H5O4aCoord) ≠ Sum.inl 0 := by decide
  have hv2 : (Sum.inr (Sum.inr (1 : Fin 2)) : s16h_H5O4aCoord) ≠
    Sum.inr (Sum.inl 0) := by decide
  rw [s16h_H5O4a_quad_explicit, s16h_H5O4a_quad_explicit]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hu1 hu2, Equiv.swap_apply_of_ne_of_ne hv1 hv2]
  ring

private theorem s16h_H5O4a_permMatrix_conj_diagonal {K : Type} [Field K]
    (σ : Equiv.Perm s16h_H5O4aCoord) (d : s16h_H5O4aCoord → K) :
    σ.permMatrix K * Matrix.diagonal d * Equiv.Perm.permMatrix K σ.symm =
      Matrix.diagonal (fun i => d (σ i)) := by
  change σ.toPEquiv.toMatrix * Matrix.diagonal d * σ.symm.toPEquiv.toMatrix =
    Matrix.diagonal (fun i => d (σ i))
  ext i j
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp only [Matrix.submatrix_apply, id_eq, Equiv.symm_symm]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · have hσ : σ i ≠ σ j := fun hσ => h (σ.injective hσ)
    rw [Matrix.diagonal_apply_ne d hσ, Matrix.diagonal_apply_ne (fun i => d (σ i)) h]

private theorem s16h_H5O4a_diagonal_mulVec_single {K : Type} [Field K]
    (d : s16h_H5O4aCoord → K) (i : s16h_H5O4aCoord) (a : K) :
    Matrix.diagonal d *ᵥ Pi.single i a = Pi.single i (d i * a) := by
  ext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne (Ne.symm h), h]

theorem s16h_H5O4a_torus_proof {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 2) {b c : K} :
    ∃ z ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)), z ≠ 1 ∧ z ^ 3 = 1 ∧
      (∃ e : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K, e ≠ 0 ∧ StatedQuadMinus 2 K b c e = 0 ∧
        ∃ ω : K, ω ≠ 0 ∧ toAddMap z e = ω • e) ∧
      ∀ t : K, t ≠ 0 → ∃ x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
        StatedQuadMinus 2 K b c x = t ∧ toAddMap z x = x := by
  classical
  have hcard : Nat.card Kˣ = 3 := by
    rw [Nat.card_units K, hK]
    norm_num
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard])
  have hω3 : ω ^ 3 = 1 := by simpa [hω] using pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  have hωK3 : (ω : K) ^ 3 = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hω3
    simpa using h
  have hωK0 : (ω : K) ≠ 0 := ω.ne_zero
  have hωK1 : (ω : K) ≠ 1 := by
    intro h
    exact hω1 (Units.ext h)
  have hωKinv3 : ((ω : K)⁻¹) ^ 3 = 1 := by
    rw [inv_pow, hωK3, inv_one]
  let σ0 : Equiv.Perm s16h_H5O4aCoord :=
    Equiv.swap (Sum.inl 0 : s16h_H5O4aCoord) (Sum.inr (Sum.inl 0))
  let d : s16h_H5O4aCoord → K := fun i =>
    if i = (Sum.inl 0 : s16h_H5O4aCoord) then (ω : K)
    else if i = (Sum.inr (Sum.inl 0) : s16h_H5O4aCoord) then (ω : K)⁻¹ else 1
  let d' : s16h_H5O4aCoord → K := fun i => d (σ0 i)
  let tmat : Matrix s16h_H5O4aCoord s16h_H5O4aCoord K := Matrix.diagonal d
  let tmat' : Matrix s16h_H5O4aCoord s16h_H5O4aCoord K := Matrix.diagonal d'
  let σmat : Matrix s16h_H5O4aCoord s16h_H5O4aCoord K := σ0.permMatrix K
  have hd_e1 : d (Sum.inl 0) = (ω : K) := by simp [d]
  have hd_e2 : d (Sum.inr (Sum.inl 0)) = (ω : K)⁻¹ := by simp [d]
  have hd_u : d (Sum.inr (Sum.inr 0)) = 1 := by simp [d]
  have hd_v : d (Sum.inr (Sum.inr 1)) = 1 := by simp [d]
  have hd_other : ∀ i : s16h_H5O4aCoord, i ≠ Sum.inl 0 → i ≠ Sum.inr (Sum.inl 0) →
      d i = 1 := by
    intro i h1 h2
    simp [d, h1, h2]
  have hσ_e1 : σ0 (Sum.inl 0) = Sum.inr (Sum.inl 0) := by simp [σ0]
  have hσ_e2 : σ0 (Sum.inr (Sum.inl 0)) = Sum.inl 0 := by simp [σ0]
  have hσ_u : σ0 (Sum.inr (Sum.inr 0)) = Sum.inr (Sum.inr 0) := by
    apply Equiv.swap_apply_of_ne_of_ne <;> decide
  have hσ_v : σ0 (Sum.inr (Sum.inr 1)) = Sum.inr (Sum.inr 1) := by
    apply Equiv.swap_apply_of_ne_of_ne <;> decide
  have hd'_e1 : d' (Sum.inl 0) = (ω : K)⁻¹ := by
    change d (σ0 (Sum.inl 0)) = (ω : K)⁻¹
    rw [hσ_e1, hd_e2]
  have hd'_e2 : d' (Sum.inr (Sum.inl 0)) = (ω : K) := by
    change d (σ0 (Sum.inr (Sum.inl 0))) = (ω : K)
    rw [hσ_e2, hd_e1]
  have hd'_u : d' (Sum.inr (Sum.inr 0)) = 1 := by
    change d (σ0 (Sum.inr (Sum.inr 0))) = 1
    rw [hσ_u, hd_u]
  have hd'_v : d' (Sum.inr (Sum.inr 1)) = 1 := by
    change d (σ0 (Sum.inr (Sum.inr 1))) = 1
    rw [hσ_v, hd_v]
  have hd_mul : ∀ i : s16h_H5O4aCoord, d i * d' i = 1 := by
    intro i
    by_cases h1 : i = Sum.inl 0
    · subst h1
      rw [hd_e1, hd'_e1, mul_inv_cancel₀ hωK0]
    · by_cases h2 : i = Sum.inr (Sum.inl 0)
      · subst h2
        rw [hd_e2, hd'_e2, inv_mul_cancel₀ hωK0]
      · have hσi : σ0 i = i := Equiv.swap_apply_of_ne_of_ne h1 h2
        rw [show d i = 1 from hd_other i h1 h2,
          show d' i = 1 by
            change d (σ0 i) = 1
            rw [hσi, hd_other i h1 h2],
          mul_one]
  have hd'_mul : ∀ i : s16h_H5O4aCoord, d' i * d i = 1 := by
    intro i
    by_cases h1 : i = Sum.inl 0
    · subst h1
      rw [hd_e1, hd'_e1, inv_mul_cancel₀ hωK0]
    · by_cases h2 : i = Sum.inr (Sum.inl 0)
      · subst h2
        rw [hd_e2, hd'_e2, mul_inv_cancel₀ hωK0]
      · have hσi : σ0 i = i := Equiv.swap_apply_of_ne_of_ne h1 h2
        rw [show d i = 1 from hd_other i h1 h2,
          show d' i = 1 by
            change d (σ0 i) = 1
            rw [hσi, hd_other i h1 h2],
          one_mul]
  have htmat_mul : tmat * tmat' = 1 := by
    change Matrix.diagonal d * Matrix.diagonal d' = 1
    rw [Matrix.diagonal_mul_diagonal,
      show (fun i => d i * d' i) = (fun _ => 1) from funext hd_mul, Matrix.diagonal_one]
  have htmat'_mul : tmat' * tmat = 1 := by
    change Matrix.diagonal d' * Matrix.diagonal d = 1
    rw [Matrix.diagonal_mul_diagonal,
      show (fun i => d' i * d i) = (fun _ => 1) from funext hd'_mul, Matrix.diagonal_one]
  let tGL : GL s16h_H5O4aCoord K := ⟨tmat, tmat', htmat_mul, htmat'_mul⟩
  have hσmat_mul : σmat * σmat = 1 := by
    change σ0.permMatrix K * σ0.permMatrix K = 1
    rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  let σGL : GL s16h_H5O4aCoord K := ⟨σmat, σmat, hσmat_mul, hσmat_mul⟩
  have hd3 : ∀ i : s16h_H5O4aCoord, d i ^ 3 = 1 := by
    intro i
    by_cases h1 : i = Sum.inl 0
    · subst h1; rw [hd_e1]; exact hωK3
    · by_cases h2 : i = Sum.inr (Sum.inl 0)
      · subst h2; rw [hd_e2]; exact hωKinv3
      · rw [hd_other i h1 h2]; simp
  have ht3 : tGL ^ 3 = 1 := by
    apply Units.ext
    change (Matrix.diagonal d) ^ 3 = 1
    rw [Matrix.diagonal_pow, show (d ^ 3 : s16h_H5O4aCoord → K) = (fun _ => 1) from funext hd3,
      Matrix.diagonal_one]
  have hσ0inv : σ0.symm = σ0 := Equiv.symm_swap _ _
  have hconj : σGL * tGL * σGL⁻¹ = tGL⁻¹ := by
    apply Units.ext
    change σmat * tmat * σmat = tmat'
    have h := s16h_H5O4a_permMatrix_conj_diagonal (σ := σ0) (d := d)
    simpa [σmat, tmat, tmat', d', hσ0inv] using h
  have htkey : tGL⁻¹ * tGL⁻¹ = tGL := by
    calc tGL⁻¹ * tGL⁻¹ = tGL⁻¹ * tGL⁻¹ * tGL ^ 3 := by rw [ht3, mul_one]
      _ = tGL := by group
  have hcomm : ⁅σGL, tGL⁆ = tGL := by
    rw [commutatorElement_def, hconj]
    exact htkey
  have htquad : ∀ v : s16h_H5O4aCoord → K,
      StatedQuadMinus 2 K b c (tmat *ᵥ v) = StatedQuadMinus 2 K b c v := by
    intro v
    rw [show tmat *ᵥ v = (fun i => d i * v i) from
      funext (fun i => Matrix.mulVec_diagonal d v i)]
    exact s16h_H5O4a_quad_scale d (by rw [hd_e1, hd_e2, mul_inv_cancel₀ hωK0]) hd_u hd_v v
  have hσquad : ∀ v : s16h_H5O4aCoord → K,
      StatedQuadMinus 2 K b c (σmat *ᵥ v) = StatedQuadMinus 2 K b c v := by
    intro v
    rw [show σmat *ᵥ v = v ∘ σ0 from by
      change σ0.permMatrix K *ᵥ v = v ∘ σ0
      exact Matrix.permMatrix_mulVec (σ := σ0) (R := K) (v := v)]
    exact s16h_H5O4a_quad_swap v
  have htIso : tGL ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c) := by
    refine Subgroup.subset_closure ?_
    intro v
    exact htquad v
  have hσIso : σGL ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c) := by
    refine Subgroup.subset_closure ?_
    intro v
    exact hσquad v
  have htComm : tGL ∈ ⁅CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c),
      CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)⁆ := by
    have h := Subgroup.commutator_mem_commutator (H₁ :=
      CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) (H₂ :=
      CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) hσIso htIso
    rwa [hcomm] at h
  have htOmega : tGL ∈ StatedOmega (StatedQuadMinus 2 K b c) := by
    simpa only [StatedOmega, CFSG.MatrixModel.isometryCore] using htComm
  let e : s16h_H5O4aCoord → K := Pi.single (Sum.inl 0) 1
  have he_ne : e ≠ 0 := by
    intro h
    have h1 := congrFun h (Sum.inl 0)
    simp [e] at h1
  have he_Q : StatedQuadMinus 2 K b c e = 0 := by
    rw [s16h_H5O4a_quad_explicit]
    simp [e]
  have hz_e : toAddMap (matAut tGL) e = (ω : K) • e := by
    rw [toAddMap_matAut]
    change Matrix.diagonal d *ᵥ e = (ω : K) • e
    ext i
    rw [Matrix.mulVec_diagonal]
    by_cases h1 : i = Sum.inl 0
    · subst h1; simp [e, hd_e1]
    · simp [e, h1]
  refine ⟨matAut tGL, ⟨⟨tGL, htOmega⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro hz1
    have h := congrArg (fun g : MulAut (StdMod s16h_H5O4aCoord K) => toAddMap g e) hz1
    rw [toAddMap_one] at h
    rw [hz_e] at h
    have h1 := congrFun h (Sum.inl 0)
    simp [e] at h1
    exact hω1 h1
  · rw [show matAut tGL = (matHom tGL : MulAut (StdMod s16h_H5O4aCoord K)) from rfl,
      ← map_pow, ht3, map_one]
  · exact ⟨e, he_ne, he_Q, (ω : K), hωK0, hz_e⟩
  · intro t ht
    obtain ⟨a, ha⟩ := isSquare_of_charTwo' (R := K) t
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) a, ?_, ?_⟩
    · have hxQ : StatedQuadMinus 2 K b c (Pi.single (Sum.inr (Sum.inr 0)) a) = a ^ 2 := by
        rw [s16h_H5O4a_quad_explicit]
        simp
      rw [hxQ, ha, pow_two]
    · show toAddMap (matAut tGL) (Pi.single (Sum.inr (Sum.inr 0)) a) =
        Pi.single (Sum.inr (Sum.inr 0)) a
      rw [toAddMap_matAut,
        s16h_H5O4a_diagonal_mulVec_single d (Sum.inr (Sum.inr 0)) a, hd_u, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

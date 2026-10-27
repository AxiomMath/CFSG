module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtPSL
public import CFSG.HardMathSupport.Foote.ModuleExclusions.ProjectiveLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem psl_odd_orderOf_of_odd_orderOf_conjAut {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (B : GL (Fin n) K) (h : Odd (orderOf (conjAut n K B))) : Odd (orderOf B) := by
  have hpow : conjAut n K (B ^ orderOf (conjAut n K B)) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  have hcenter : B ^ orderOf (conjAut n K B) ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    obtain ⟨l, hl⟩ :=
      CFSG.HardMathSupport.Foote.ModuleExclusions.exists_scalar_of_conjAut_eq_one hpow
    exact ⟨l, hl.symm⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨u, hu⟩ := hcenter
  have hpow_odd : Odd (orderOf (B ^ orderOf (conjAut n K B))) := by
    exact Odd.of_dvd_nat (CFSG.StandardType.AutPSL.odd_card_units (K := K))
      (orderOf_dvd_of_pow_eq_one (by
        rw [← hu, ← map_pow, pow_card_eq_one', map_one]))
  have hdvd : orderOf B ∣ orderOf (conjAut n K B) *
      orderOf (B ^ orderOf (conjAut n K B)) :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
  exact Odd.of_dvd_nat (Odd.mul h hpow_odd) hdvd

private theorem ggPSLAh_one_add_sq {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (N : Matrix (Fin n) (Fin n) K) (hN : N * N = 0) : (1 + N) * (1 + N) = 1 := by
  have h2 : N + N = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero (N i j)
  calc (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
    _ = 1 := by simp [h2, hN]

private theorem ggPSLAh_smul_mul_self_eq_zero {n : ℕ} {K : Type} [Field K] (t : K)
    (N : Matrix (Fin n) (Fin n) K) (hN : N * N = 0) : (t • N) * (t • N) = 0 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN, smul_zero]

private theorem ggPSLAh_sigma_eq_one_of_fixed {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (σ : K ≃+* K) (E E' : Matrix (Fin n) (Fin n) K) (hE0 : E ≠ 0)
    (hE2 : E * E = 0) (hE'2 : E' * E' = 0)
    (x w : K → SpecialLinearGroup (Fin n) K)
    (hx : ∀ t, (x t : Matrix (Fin n) (Fin n) K) = 1 + t • E)
    (hw : ∀ t, (w t : Matrix (Fin n) (Fin n) K) = 1 + σ t • E')
    (hfix : ∀ t, proj n K (w t) = proj n K (x t)) : σ = 1 := by
  have hx2 : ∀ t, (x t : Matrix (Fin n) (Fin n) K) * (x t : Matrix (Fin n) (Fin n) K) = 1 := by
    intro t
    rw [hx t]
    exact ggPSLAh_one_add_sq (t • E) (ggPSLAh_smul_mul_self_eq_zero t E hE2)
  have hw2 : ∀ t, (w t : Matrix (Fin n) (Fin n) K) * (w t : Matrix (Fin n) (Fin n) K) = 1 := by
    intro t
    rw [hw t]
    exact ggPSLAh_one_add_sq (σ t • E') (ggPSLAh_smul_mul_self_eq_zero (σ t) E' hE'2)
  obtain ⟨i, j, hij⟩ : ∃ i j, E i j ≠ 0 := by
    by_contra hcon
    apply hE0
    ext i j
    by_contra h'
    exact hcon ⟨i, j, h'⟩
  have key : ∀ t, (w t : Matrix (Fin n) (Fin n) K) = (x t : Matrix (Fin n) (Fin n) K) := by
    intro t
    have hmem : (w t)⁻¹ * x t ∈ scalars n K := (proj_eq_proj_iff).1 (hfix t)
    obtain ⟨c, _hc, hc⟩ := (mem_scalars).1 hmem
    have h2 : (x t : Matrix (Fin n) (Fin n) K) =
        (w t : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K) := by
      calc (x t : Matrix (Fin n) (Fin n) K)
          = ((w t * ((w t)⁻¹ * x t) : SpecialLinearGroup (Fin n) K) :
              Matrix (Fin n) (Fin n) K) := by rw [mul_inv_cancel_left]
        _ = (w t : Matrix (Fin n) (Fin n) K) *
              (((w t)⁻¹ * x t : SpecialLinearGroup (Fin n) K) :
                Matrix (Fin n) (Fin n) K) := rfl
        _ = (w t : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K) := by rw [hc]
    have hcomm : scalar (Fin n) (c : K) * (w t : Matrix (Fin n) (Fin n) K) =
        (w t : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K) :=
      (Matrix.scalar_commute (c : K) (fun r => mul_comm (c : K) r)
        (w t : Matrix (Fin n) (Fin n) K)).eq
    have hsc : ((w t : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K)) *
        ((w t : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K)) =
        scalar (Fin n) (c : K) * scalar (Fin n) (c : K) := by
      have h1 : ((w t : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K)) *
          ((w t : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K)) =
          (w t : Matrix (Fin n) (Fin n) K) *
            (scalar (Fin n) (c : K) * (w t : Matrix (Fin n) (Fin n) K)) *
            scalar (Fin n) (c : K) := by noncomm_ring
      rw [h1, hcomm]
      have h2 : (w t : Matrix (Fin n) (Fin n) K) *
          ((w t : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (c : K)) *
          scalar (Fin n) (c : K) =
          ((w t : Matrix (Fin n) (Fin n) K) * (w t : Matrix (Fin n) (Fin n) K)) *
            (scalar (Fin n) (c : K) * scalar (Fin n) (c : K)) := by noncomm_ring
      rw [h2, hw2 t, Matrix.one_mul]
    have hx2t := hx2 t
    rw [h2, hsc] at hx2t
    have hii := congrFun (congrFun hx2t i) i
    have hcc : (scalar (Fin n) (c : K) : Matrix (Fin n) (Fin n) K) *
        scalar (Fin n) (c : K) = scalar (Fin n) ((c : K) * c) :=
      (map_mul (Matrix.scalar (Fin n)) (c : K) (c : K)).symm
    rw [hcc] at hii
    have hc2 : (c : K) ^ 2 = 1 := by
      simpa [Matrix.scalar_apply, Matrix.one_apply, pow_two] using hii
    have hc1 : (c : K) = 1 := CharTwo.sq_inj.1 (by rw [hc2, one_pow])
    rw [hc1] at h2
    simpa using h2.symm
  have hEq : ∀ t, σ t • E' = t • E := by
    intro t
    have h := key t
    rw [hw t, hx t] at h
    exact add_left_cancel h
  have hE' : E' = E := by
    have h := hEq 1
    simpa using h
  have hzero : ∀ t, (σ t - t) • E = 0 := by
    intro t
    have h := hEq t
    rw [hE'] at h
    rw [sub_smul, h, sub_self]
  have hσeq : ∀ t, σ t = t := by
    intro t
    have h := congrFun (congrFun (hzero t) i) j
    simp only [Matrix.smul_apply, Pi.zero_apply] at h
    have h2 : σ t - t = 0 := by
      rcases mul_eq_zero.1 h with h3 | h3
      · exact h3
      · exact absurd h3 hij
    exact sub_eq_zero.1 h2
  exact RingEquiv.ext hσeq

private theorem ggPSLAh_conj_one_add {n : ℕ} {K : Type} [Field K]
    (A : GL (Fin n) K) (t : K) (N : Matrix (Fin n) (Fin n) K) :
    (A : Matrix (Fin n) (Fin n) K) * (1 + t • N) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + t • ((A : Matrix (Fin n) (Fin n) K) * N *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
  rw [show (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]

private theorem ggPSLAh_conj_sq_zero {n : ℕ} {K : Type} [Field K]
    (A : GL (Fin n) K) (N : Matrix (Fin n) (Fin n) K) (hN : N * N = 0) :
    ((A : Matrix (Fin n) (Fin n) K) * N *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
      ((A : Matrix (Fin n) (Fin n) K) * N *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 0 := by
  have hAA : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (A : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((A : Matrix (Fin n) (Fin n) K) * N *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((A : Matrix (Fin n) (Fin n) K) * N *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      = (A : Matrix (Fin n) (Fin n) K) * N *
          (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K)) * N *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by noncomm_ring
    _ = (A : Matrix (Fin n) (Fin n) K) * (N * N) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hAA]; noncomm_ring
    _ = 0 := by rw [hN, Matrix.mul_zero, Matrix.zero_mul]

private theorem ggPSLAh_map_one_add_smul {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (t : K)
    (E : Matrix (Fin n) (Fin n) K) :
    (1 + t • E).map σ.toRingHom = 1 + σ t • E.map σ.toRingHom := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

theorem psl_field_unipotent_not_fixed {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (σ : K ≃+* K) (hσ : σ ≠ 1) (A : GL (Fin n) K) (ε : ℕ) (hε : ε < 2)
    (E : Matrix (Fin n) (Fin n) K) (hE0 : E ≠ 0) (hE2 : E * E = 0)
    (x : K → SpecialLinearGroup (Fin n) K)
    (hx : ∀ t, (x t : Matrix (Fin n) (Fin n) K) = 1 + t • E) :
    let α : MulAut (projectiveSL n K) := conjAut n K A * (fieldAut n K σ * AutPSL.graphAut ^ ε)
    ¬ ∀ t : K, α (proj n K (x t)) = proj n K (x t) := by
  change ¬ ∀ t : K,
    ((conjAut n K A * (fieldAut n K σ * AutPSL.graphAut ^ ε)) :
        MulAut (projectiveSL n K)) (proj n K (x t)) = proj n K (x t)
  intro hfix
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · have hfix0 : ∀ t, (conjAut n K A * fieldAut n K σ) (proj n K (x t)) = proj n K (x t) := by
      intro t
      have := hfix t
      simpa only [pow_zero, mul_one] using this
    set G : Matrix (Fin n) (Fin n) K := E.map σ.toRingHom with hGdef
    have hG2 : G * G = 0 := by
      rw [hGdef, ← Matrix.map_mul, hE2]
      simp
    set E' : Matrix (Fin n) (Fin n) K :=
      (A : Matrix (Fin n) (Fin n) K) * G * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      with hE'def
    have hE'2 : E' * E' = 0 := by
      rw [hE'def]
      exact ggPSLAh_conj_sq_zero A G hG2
    set w : K → SpecialLinearGroup (Fin n) K := fun t =>
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A
        (SpecialLinearGroup.map σ.toRingHom (x t)) with hwdef
    have hw : ∀ t, (w t : Matrix (Fin n) (Fin n) K) = 1 + σ t • E' := by
      intro t
      rw [hwdef, hE'def, hGdef, coe_slConjugation, SpecialLinearGroup.map_apply_coe, hx t,
        RingHom.mapMatrix_apply, ggPSLAh_map_one_add_smul]
      exact ggPSLAh_conj_one_add A (σ t) (E.map σ.toRingHom)
    have hfixw : ∀ t, proj n K (w t) = proj n K (x t) := by
      intro t
      have := hfix0 t
      simpa only [hwdef, MulAut.mul_apply, fieldAut_proj, conjAut_proj] using this
    exact hσ (ggPSLAh_sigma_eq_one_of_fixed σ E E' hE0 hE2 hE'2 x w hx hw hfixw)
  · have hfix1 : ∀ t, ((conjAut n K A * (fieldAut n K σ * AutPSL.graphAut)) :
        MulAut (projectiveSL n K)) (proj n K (x t)) = proj n K (x t) := by
      intro t
      have := hfix t
      simpa only [pow_one] using this
    set G : Matrix (Fin n) (Fin n) K :=
      (Eᵀ.submatrix Fin.revPerm Fin.revPerm).map σ.toRingHom with hGdef
    have hG2 : G * G = 0 := by
      rw [hGdef, ← Matrix.map_mul]
      have hsub : (Eᵀ.submatrix Fin.revPerm Fin.revPerm) *
          (Eᵀ.submatrix Fin.revPerm Fin.revPerm) =
          (E * E)ᵀ.submatrix Fin.revPerm Fin.revPerm := by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul]
      rw [hsub, hE2]
      simp
    set E' : Matrix (Fin n) (Fin n) K :=
      (A : Matrix (Fin n) (Fin n) K) * G * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      with hE'def
    have hE'2 : E' * E' = 0 := by
      rw [hE'def]
      exact ggPSLAh_conj_sq_zero A G hG2
    set w : K → SpecialLinearGroup (Fin n) K := fun t =>
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A
        (SpecialLinearGroup.map σ.toRingHom (AutPSL.gammaSL (x t))) with hwdef
    have hw : ∀ t, (w t : Matrix (Fin n) (Fin n) K) = 1 + σ t • E' := by
      intro t
      have hxinv : (((x t)⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          1 + t • E := by
        have hsq : x t * x t = 1 := by
          apply Subtype.ext
          change (x t : Matrix (Fin n) (Fin n) K) * (x t : Matrix (Fin n) (Fin n) K) = 1
          rw [hx t]
          exact ggPSLAh_one_add_sq (t • E) (ggPSLAh_smul_mul_self_eq_zero t E hE2)
        rw [inv_eq_of_mul_eq_one_right hsq, hx t]
      have hgamma : ((((x t)⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)ᵀ.submatrix Fin.revPerm Fin.revPerm) =
          1 + t • (Eᵀ.submatrix Fin.revPerm Fin.revPerm) := by
        rw [hxinv]
        ext i j
        simp [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.one_apply]
      rw [hwdef, hE'def, hGdef, coe_slConjugation, SpecialLinearGroup.map_apply_coe,
        AutPSL.coe_gammaSL, hgamma, RingHom.mapMatrix_apply, ggPSLAh_map_one_add_smul]
      exact ggPSLAh_conj_one_add A (σ t) G
    have hfixw : ∀ t, proj n K (w t) = proj n K (x t) := by
      intro t
      have := hfix1 t
      simpa only [hwdef, MulAut.mul_apply, AutPSL.graphAut_proj, fieldAut_proj, conjAut_proj]
        using this
    exact hσ (ggPSLAh_sigma_eq_one_of_fixed σ E E' hE0 hE2 hE'2 x w hx hw hfixw)

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm

private theorem ggPSLS1_minpoly_squarefree {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (B : GL (Fin n) K) (hB : Odd (orderOf B)) :
    Squarefree (minpoly K (Matrix.toLin' (B : Matrix (Fin n) (Fin n) K))) := by
  have hK : (orderOf B : K) ≠ 0 := by
    intro hc
    have hdvd : 2 ∣ orderOf B := (CharP.cast_eq_zero_iff K 2 (orderOf B)).mp hc
    obtain ⟨t, ht⟩ := hdvd
    obtain ⟨k, hk⟩ := hB
    omega
  refine squarefree_minpoly_of_pow_eq_one hK ?_
  rw [show Matrix.toLin' (B : Matrix (Fin n) (Fin n) K) =
      (Matrix.toLinAlgEquiv' (B : Matrix (Fin n) (Fin n) K) : Module.End K (Fin n → K)) from
    (toLinAlgEquiv'_eq_toLin' (B : Matrix (Fin n) (Fin n) K)).symm]
  rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]

private theorem ggPSLS1_matrix_comm_of_le_one {F : Type} [Field F] {m : ℕ} (hm : m ≤ 1)
    (A Bm : Matrix (Fin m) (Fin m) F) : A * Bm = Bm * A := by
  haveI : Subsingleton (Fin m) := Fin.subsingleton_iff_le_one.mpr hm
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Subsingleton.elim k i, Subsingleton.elim j i, mul_comm]

private theorem ggPSLS1_mem_commutant_toLinAlgEquiv' {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K)
    (hX : X * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * X) :
    Matrix.toLinAlgEquiv' X ∈ commutant (Matrix.toLin' (B : Matrix (Fin n) (Fin n) K)) := by
  rw [mem_commutant]
  change Matrix.toLinAlgEquiv' X * Matrix.toLin' (B : Matrix (Fin n) (Fin n) K) =
    Matrix.toLin' (B : Matrix (Fin n) (Fin n) K) * Matrix.toLinAlgEquiv' X
  rw [(toLinAlgEquiv'_eq_toLin' (B : Matrix (Fin n) (Fin n) K)).symm]
  rw [← map_mul, ← map_mul, hX]

private theorem ggPSLS1_commutantToMat_toLinAlgEquiv' {n : ℕ} {K : Type} [Field K]
    (x : Module.End K (Fin n → K)) (X : Matrix (Fin n) (Fin n) K)
    (hX : Matrix.toLinAlgEquiv' X ∈ commutant x) :
    commutantToMat x ⟨Matrix.toLinAlgEquiv' X, hX⟩ = X := by
  show (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
    Module.End K (Fin n → K)).symm (Matrix.toLinAlgEquiv' X) = X
  exact AlgEquiv.symm_apply_apply _ _

private theorem ggPSLS1_exists_sq_zero_of_two_le_mult {n : ℕ} {K : Type} [Field K]
    (x : Module.End K (Fin n → K)) (hx : Squarefree (minpoly K x))
    (a : primaryFactors x) (ha : 2 ≤ primaryMultiplicity x (a : K[X])) :
    ∃ r : commutant x, r ≠ 0 ∧ r * r = 0 := by
  classical
  have h0 : 0 < primaryMultiplicity x (a : K[X]) := by omega
  have h1 : 1 < primaryMultiplicity x (a : K[X]) := by omega
  have hne : (⟨1, h1⟩ : Fin (primaryMultiplicity x (a : K[X]))) ≠ ⟨0, h0⟩ := by
    intro hc
    exact Nat.one_ne_zero (by simpa using congrArg Fin.val hc)
  set Ea : Matrix (Fin (primaryMultiplicity x (a : K[X])))
      (Fin (primaryMultiplicity x (a : K[X]))) (AdjoinRoot (a : K[X])) :=
    Matrix.single ⟨0, h0⟩ ⟨1, h1⟩ (1 : AdjoinRoot (a : K[X])) with hEa
  set E : (b : primaryFactors x) →
      Matrix (Fin (primaryMultiplicity x (b : K[X])))
        (Fin (primaryMultiplicity x (b : K[X]))) (AdjoinRoot (b : K[X])) :=
    Function.update (fun _ => 0) a Ea with hE
  have hEa2 : Ea * Ea = 0 := by
    rw [hEa]
    exact Matrix.single_mul_single_of_ne (1 : AdjoinRoot (a : K[X]))
      (⟨0, h0⟩ : Fin (primaryMultiplicity x (a : K[X])))
      (⟨1, h1⟩ : Fin (primaryMultiplicity x (a : K[X])))
      (⟨0, h0⟩ : Fin (primaryMultiplicity x (a : K[X]))) hne (1 : AdjoinRoot (a : K[X]))
  have hEa0 : Ea ≠ 0 := by
    intro hzero
    have h1' : Ea ⟨0, h0⟩ ⟨1, h1⟩ = 0 := by
      have := congrFun (congrFun hzero ⟨0, h0⟩) ⟨1, h1⟩
      simpa using this
    have h2 : (1 : AdjoinRoot (a : K[X])) = 0 := by
      rw [hEa] at h1'
      simpa [Matrix.single_apply] using h1'
    exact one_ne_zero h2
  have hE2 : E * E = 0 := by
    rw [hE]
    funext b
    by_cases hb : b = a
    · subst hb
      rw [Pi.mul_apply, Function.update_self]
      simpa using hEa2
    · rw [Pi.mul_apply, Function.update_of_ne hb]
      simp
  have hE0 : E ≠ 0 := by
    intro hzero
    apply hEa0
    have h1' : E a = 0 := by
      have := congrFun hzero a
      simpa using this
    rw [hE] at h1'
    rw [Function.update_self] at h1'
    exact h1'
  refine ⟨(commutantEquivMatrix hx).symm E, ?_, ?_⟩
  · intro hzero
    apply hE0
    have h := congrArg (commutantEquivMatrix hx) hzero
    simpa using h
  · apply (commutantEquivMatrix hx).injective
    rw [map_mul, AlgEquiv.apply_symm_apply, hE2, map_zero]

theorem psl_commutant_comm_of_no_square_zero {n : ℕ} {K : Type} [Field K]
    [CharP K 2] (B : GL (Fin n) K) (hB : Odd (orderOf B))
    (h : ∀ E : Matrix (Fin n) (Fin n) K, E * E = 0 →
      E * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * E → E = 0)
    (X Y : Matrix (Fin n) (Fin n) K)
    (hX : X * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * X)
    (hY : Y * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * Y) :
    X * Y = Y * X := by
  classical
  set x : Module.End K (Fin n → K) := Matrix.toLin' (B : Matrix (Fin n) (Fin n) K) with hx
  have hx_sq : Squarefree (minpoly K x) := by
    rw [hx]
    exact ggPSLS1_minpoly_squarefree B hB
  have hsmall : ∀ a : primaryFactors x, primaryMultiplicity x (a : K[X]) ≤ 1 := by
    intro a
    by_contra hlt
    have hlt2 : 2 ≤ primaryMultiplicity x (a : K[X]) := by omega
    obtain ⟨r, hr0, hr2⟩ := ggPSLS1_exists_sq_zero_of_two_le_mult x hx_sq a hlt2
    set M : Matrix (Fin n) (Fin n) K := commutantToMat x r with hM
    have hM2 : M * M = 0 := by
      rw [hM]
      have hstep : commutantToMat x (r * r) = commutantToMat x 0 := by rw [hr2]
      simpa only [map_mul, map_zero] using hstep
    have hM0 : M ≠ 0 := by
      intro hMzero
      apply hr0
      apply commutantToMat_injective x
      rw [← hM, hMzero, map_zero]
    have hMcomm : M * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * M := by
      have hxmem : x ∈ commutant x := (mem_commutant x).mpr (Commute.refl x)
      have hrx : r * ⟨x, hxmem⟩ = ⟨x, hxmem⟩ * r := by
        apply Subtype.ext
        exact ((mem_commutant x).mp r.2).eq
      have hcongr := congrArg (commutantToMat x) hrx
      simp only [map_mul] at hcongr
      have hxlift : commutantToMat x ⟨x, hxmem⟩ = (B : Matrix (Fin n) (Fin n) K) := by
        show (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
          Module.End K (Fin n → K)).symm x = (B : Matrix (Fin n) (Fin n) K)
        rw [hx, (toLinAlgEquiv'_eq_toLin' (B : Matrix (Fin n) (Fin n) K)).symm]
        exact AlgEquiv.symm_apply_apply _ _
      rw [hxlift] at hcongr
      rw [hM]
      exact hcongr
    exact hM0 (h M hM2 hMcomm)
  have htarget : ∀ u v : (a : primaryFactors x) →
      Matrix (Fin (primaryMultiplicity x (a : K[X])))
        (Fin (primaryMultiplicity x (a : K[X]))) (AdjoinRoot (a : K[X])), u * v = v * u := by
    intro u v
    funext a
    rw [Pi.mul_apply, Pi.mul_apply]
    exact ggPSLS1_matrix_comm_of_le_one (hsmall a) (u a) (v a)
  have hcommC : ∀ r s : commutant x, r * s = s * r := by
    intro r s
    apply (commutantEquivMatrix hx_sq).injective
    rw [map_mul, map_mul]
    exact htarget _ _
  have hXmem : Matrix.toLinAlgEquiv' X ∈ commutant x := by
    rw [hx]
    exact ggPSLS1_mem_commutant_toLinAlgEquiv' B X hX
  have hYmem : Matrix.toLinAlgEquiv' Y ∈ commutant x := by
    rw [hx]
    exact ggPSLS1_mem_commutant_toLinAlgEquiv' B Y hY
  have hmap := congrArg (commutantToMat x)
    (hcommC ⟨Matrix.toLinAlgEquiv' X, hXmem⟩ ⟨Matrix.toLinAlgEquiv' Y, hYmem⟩)
  simp only [map_mul] at hmap
  rw [ggPSLS1_commutantToMat_toLinAlgEquiv' x X hXmem,
    ggPSLS1_commutantToMat_toLinAlgEquiv' x Y hYmem] at hmap
  exact hmap

private noncomputable def ggPSLS2_slConj {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (x : SpecialLinearGroup (Fin n) K) : SpecialLinearGroup (Fin n) K :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B x

private theorem ggPSLS2_slConj_mul {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (x y : SpecialLinearGroup (Fin n) K) :
    ggPSLS2_slConj B (x * y) = ggPSLS2_slConj B x * ggPSLS2_slConj B y := by
  exact map_mul
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B) x y

private noncomputable def ggPSLS2_z {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (x : SpecialLinearGroup (Fin n) K) : SpecialLinearGroup (Fin n) K :=
  ggPSLS2_slConj B x * x⁻¹

private theorem ggPSLS2_z_mem_center {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (L : Subgroup (projectiveSL n K))
    (hL : ∀ g ∈ L, conjAut n K B g = g)
    (x : L.comap (proj n K)) :
    ggPSLS2_z B (x : SpecialLinearGroup (Fin n) K) ∈
      Subgroup.center (SpecialLinearGroup (Fin n) K) := by
  refine scalars_le_center n K ?_
  rw [← proj_eq_one_iff]
  rw [ggPSLS2_z, ggPSLS2_slConj, map_mul, map_inv, ← conjAut_proj]
  rw [hL (proj n K (x : SpecialLinearGroup (Fin n) K)) x.2]
  exact mul_inv_cancel _

private theorem ggPSLS2_z_mul {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (x y : SpecialLinearGroup (Fin n) K)
    (hzy : ggPSLS2_z B y ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) :
    ggPSLS2_z B (x * y) = ggPSLS2_z B x * ggPSLS2_z B y := by
  have h1 : x * (ggPSLS2_slConj B y * y⁻¹) = (ggPSLS2_slConj B y * y⁻¹) * x := by
    have h := Subgroup.mem_center_iff.mp hzy x
    simpa only [ggPSLS2_z] using h
  simp only [ggPSLS2_z, ggPSLS2_slConj_mul, _root_.mul_inv_rev]
  calc
    (ggPSLS2_slConj B x * ggPSLS2_slConj B y) * (y⁻¹ * x⁻¹)
        = (ggPSLS2_slConj B x * x⁻¹) *
            (x * (ggPSLS2_slConj B y * y⁻¹) * x⁻¹) := by group
    _ = (ggPSLS2_slConj B x * x⁻¹) *
            ((ggPSLS2_slConj B y * y⁻¹) * x * x⁻¹) := by rw [h1]
    _ = (ggPSLS2_slConj B x * x⁻¹) * (ggPSLS2_slConj B y * y⁻¹) := by group

private noncomputable def ggPSLS2_zHom {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (L : Subgroup (projectiveSL n K))
    (hL : ∀ g ∈ L, conjAut n K B g = g) :
    L.comap (proj n K) →* Subgroup.center (SpecialLinearGroup (Fin n) K) where
  toFun x := ⟨ggPSLS2_z B (x : SpecialLinearGroup (Fin n) K),
    ggPSLS2_z_mem_center B L hL x⟩
  map_one' := Subtype.ext (by simp [ggPSLS2_z, ggPSLS2_slConj])
  map_mul' := fun x y => Subtype.ext
    (ggPSLS2_z_mul B (x : SpecialLinearGroup (Fin n) K) (y : SpecialLinearGroup (Fin n) K)
      (ggPSLS2_z_mem_center B L hL y))

private theorem ggPSLS2_ker_commutes {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (L : Subgroup (projectiveSL n K))
    (hL : ∀ g ∈ L, conjAut n K B g = g)
    (x : (ggPSLS2_zHom B L hL).ker) :
    ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) *
        (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) *
        ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) := by
  have hx1 : ggPSLS2_z B ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) = 1 := by
    have h := MonoidHom.mem_ker.mp x.2
    exact congrArg (fun z : Subgroup.center (SpecialLinearGroup (Fin n) K) =>
      (z : SpecialLinearGroup (Fin n) K)) h
  have hsl : ggPSLS2_slConj B ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) =
      ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) := by
    have h := hx1
    rw [ggPSLS2_z] at h
    calc ggPSLS2_slConj B ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K)
        = ggPSLS2_slConj B ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K)
            * (((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K))⁻¹
            * ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) := by group
      _ = 1 * ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) := by rw [h]
      _ = ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) := one_mul _
  have hmat : (B : Matrix (Fin n) (Fin n) K) *
        ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) *
        ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) := by
    have h := congrArg (fun g : SpecialLinearGroup (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K)) hsl
    simpa [ggPSLS2_slConj, coe_slConjugation] using h
  have hBB : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmain : ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) *
        (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) *
        ((x : L.comap (proj n K)) : SpecialLinearGroup (Fin n) K) *
        (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (B : Matrix (Fin n) (Fin n) K)) := by
    conv_lhs => rw [← hmat]
    noncomm_ring
  rw [hmain, hBB, mul_one]

private theorem ggPSLS2_ker_comm {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (L : Subgroup (projectiveSL n K))
    (hL : ∀ g ∈ L, conjAut n K B g = g)
    (hcomm : ∀ X Y : Matrix (Fin n) (Fin n) K,
      X * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * X →
      Y * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * Y →
      X * Y = Y * X)
    (x y : (ggPSLS2_zHom B L hL).ker) : x * y = y * x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hcomm _ _ (ggPSLS2_ker_commutes B L hL x) (ggPSLS2_ker_commutes B L hL y)

private theorem ggPSLS2_ker_isSolvable {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (L : Subgroup (projectiveSL n K))
    (hL : ∀ g ∈ L, conjAut n K B g = g)
    (hcomm : ∀ X Y : Matrix (Fin n) (Fin n) K,
      X * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * X →
      Y * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * Y →
      X * Y = Y * X) :
    Group.IsSolvable (ggPSLS2_zHom B L hL).ker := by
  exact Group.isSolvable_of_comm (ggPSLS2_ker_comm B L hL hcomm)

private theorem ggPSLS2_range_isSolvable {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (L : Subgroup (projectiveSL n K))
    (hL : ∀ g ∈ L, conjAut n K B g = g) :
    Group.IsSolvable (ggPSLS2_zHom B L hL).range := by
  refine Group.isSolvable_of_comm (G := (ggPSLS2_zHom B L hL).range) (fun a b => ?_)
  apply Subtype.ext
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp a.1.2 b.1.1).symm

theorem psl_solvable_of_commutant_comm {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K)
    (hcomm : ∀ X Y : Matrix (Fin n) (Fin n) K,
      X * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * X →
      Y * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * Y → X * Y = Y * X)
    (L : Subgroup (projectiveSL n K)) (hL : ∀ g ∈ L, conjAut n K B g = g) :
    IsSolvable L := by
  let L' : Subgroup (SpecialLinearGroup (Fin n) K) := L.comap (proj n K)
  let φ : L' →* Subgroup.center (SpecialLinearGroup (Fin n) K) := ggPSLS2_zHom B L hL
  haveI : Group.IsSolvable φ.ker := ggPSLS2_ker_isSolvable B L hL hcomm
  haveI : Group.IsSolvable φ.range := ggPSLS2_range_isSolvable B L hL
  haveI : Group.IsSolvable L' :=
    Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  let f : L' →* L := MonoidHom.codRestrict ((proj n K).comp L'.subtype) L (fun x => x.2)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := proj_surjective n K (y : projectiveSL n K)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show proj n K x ∈ L
      rw [hx]
      exact y.2
    · apply Subtype.ext
      exact hx
  exact Group.isSolvable_of_surjective (f := f) hf

private theorem ggPSLA_det_one_add {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (N : Matrix (Fin n) (Fin n) K) (hN : N * N = 0) : (1 + N).det = 1 := by
  have hsq : (1 + N) * (1 + N) = 1 := ggPSLAh_one_add_sq N hN
  have hd : (1 + N).det * (1 + N).det = 1 := by
    rw [← Matrix.det_mul, hsq, Matrix.det_one]
  have h2 : (1 + N).det ^ 2 = (1 : K) ^ 2 := by
    rw [pow_two, pow_two, hd, one_mul]
  exact CharTwo.sq_inj.1 h2

private theorem ggPSLA_conj_E {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (E : Matrix (Fin n) (Fin n) K)
    (h : E * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * E) :
    (B : Matrix (Fin n) (Fin n) K) * E *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = E := by
  rw [← h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem pslFieldNone_holds : PSLFieldNone := by
  intro n K _ _ _ hn A B σ ε hε hσ
  dsimp only
  intro hα2 hodd hcomm hfix L₁ hL₁
  have hB : Odd (orderOf B) := psl_odd_orderOf_of_odd_orderOf_conjAut B hodd
  by_cases hE : ∃ E : Matrix (Fin n) (Fin n) K, E ≠ 0 ∧ E * E = 0 ∧
      E * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * E
  · obtain ⟨E, hE0, hE2, hEB⟩ := hE
    let x : K → SpecialLinearGroup (Fin n) K := fun t =>
      ⟨1 + t • E, ggPSLA_det_one_add (t • E) (ggPSLAh_smul_mul_self_eq_zero t E hE2)⟩
    have hx : ∀ t, (x t : Matrix (Fin n) (Fin n) K) = 1 + t • E := fun _ => rfl
    have hBE : (B : Matrix (Fin n) (Fin n) K) * E *
        ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = E :=
      ggPSLA_conj_E B E hEB
    have hconj : ∀ t, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        n K B (x t) = x t := by
      intro t
      apply Subtype.ext
      rw [coe_slConjugation, hx t, ggPSLAh_conj_one_add, hBE]
    have hfixx : ∀ t, conjAut n K B (proj n K (x t)) = proj n K (x t) := by
      intro t
      rw [conjAut_proj, hconj t]
    exact absurd (fun t => hfix _ (hfixx t))
      (psl_field_unipotent_not_fixed σ hσ A ε hε E hE0 hE2 x hx)
  · have hno : ∀ E : Matrix (Fin n) (Fin n) K, E * E = 0 →
        E * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * E →
        E = 0 := by
      intro E hE2 hEB
      by_contra hE0
      exact hE ⟨E, hE0, hE2, hEB⟩
    have hcomm' : ∀ X Y : Matrix (Fin n) (Fin n) K,
        X * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * X →
        Y * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * Y →
        X * Y = Y * X :=
      fun X Y hX hY => psl_commutant_comm_of_no_square_zero B hB hno X Y hX hY
    exact psl_solvable_of_commutant_comm B hcomm' L₁ hL₁

end CFSG.StandardType

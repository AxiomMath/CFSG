module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

variable (K) in
@[expose] def uc22pwI3TorusUnits : Subgroup (Fin 3 → Kˣ) where
  carrier := {v | v 0 * v 1 * v 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro v w hv hw
    simp only [Pi.mul_apply, Set.mem_setOf_eq] at hv hw ⊢
    calc (v 0 * w 0) * (v 1 * w 1) * (v 2 * w 2)
        = (v 0 * v 1 * v 2) * (w 0 * w 1 * w 2) := by ac_rfl
      _ = 1 := by rw [hv, hw, one_mul]
  inv_mem' := by
    intro v hv
    simp only [Pi.inv_apply, Set.mem_setOf_eq] at hv ⊢
    simpa [_root_.mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using congrArg Inv.inv hv

variable (K) in
@[expose] def uc22pwI3TorusHom : uc22pwI3TorusUnits K →* SpecialLinearGroup (Fin 3) K where
  toFun v := ⟨Matrix.diagonal fun i => ((v.1 i : Kˣ) : K), by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using congrArg (fun u : Kˣ => (u : K)) v.2⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => (((1 : Fin 3 → Kˣ) i : Kˣ) : K)) = 1
    exact Matrix.diagonal_one
  map_mul' v w := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => (((v * w).1 i : Kˣ) : K)) =
      Matrix.diagonal (fun i => ((v.1 i : Kˣ) : K)) *
        Matrix.diagonal (fun i => ((w.1 i : Kˣ) : K))
    rw [Matrix.diagonal_mul_diagonal]
    rfl

variable (K) in
@[expose] noncomputable def uc22pwI3TorusMap [CharP K 2] (ε : Bool) (i : ℕ)
    (d : SpecialLinearGroup (Fin 3) K) : SpecialLinearGroup (Fin 3) K :=
  if ε then uc22pwI3Jsl K * (d ^ 2 ^ i)⁻¹ * uc22pwI3Jsl K else d ^ 2 ^ i

theorem uc22pwI3TorusHom_inv_coe (v : uc22pwI3TorusUnits K) :
    (((uc22pwI3TorusHom K v)⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun i => (((v.1 i)⁻¹ : Kˣ) : K)) := by
  have h : (uc22pwI3TorusHom K v)⁻¹ = uc22pwI3TorusHom K v⁻¹ :=
    (map_inv (uc22pwI3TorusHom K) v).symm
  rw [h]
  rfl

theorem uc22pwI3TorusHom_pow_coe (v : uc22pwI3TorusUnits K) (i : ℕ) :
    (((uc22pwI3TorusHom K v) ^ 2 ^ i : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun j => (((v.1 j : Kˣ) : K) ^ 2 ^ i)) := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  change (Matrix.diagonal (fun j => ((v.1 j : Kˣ) : K))) ^ 2 ^ i =
    Matrix.diagonal (fun j => (((v.1 j : Kˣ) : K) ^ 2 ^ i))
  rw [Matrix.diagonal_pow]
  rfl

theorem exists_uc22pwI3TorusHom_eq_of_mem_diagonalTorus
    {d : SpecialLinearGroup (Fin 3) K} (hd : d ∈ SpecialLinearGroup.diagonalTorus K 3) :
    ∃ v : uc22pwI3TorusUnits K, uc22pwI3TorusHom K v = d := by
  have hdiag : (d : Matrix (Fin 3) (Fin 3) K).IsDiag :=
    SpecialLinearGroup.mem_diagonalTorus_iff.mp hd
  set w : Fin 3 → K := Matrix.diag (d : Matrix (Fin 3) (Fin 3) K) with hw
  have hcoe : Matrix.diagonal w = (d : Matrix (Fin 3) (Fin 3) K) := hdiag.diagonal_diag
  have hdet : w 0 * w 1 * w 2 = 1 := by
    have h := d.prop
    rw [← hcoe, Matrix.det_diagonal, Fin.prod_univ_three] at h
    exact h
  have hne : ∀ i : Fin 3, w i ≠ 0 := by
    intro i hi
    have hzero : w 0 * w 1 * w 2 = 0 := by
      fin_cases i
      · have hi' : w 0 = 0 := by simpa using hi
        rw [hi']; ring
      · have hi' : w 1 = 0 := by simpa using hi
        rw [hi']; ring
      · have hi' : w 2 = 0 := by simpa using hi
        rw [hi']; ring
    rw [hdet] at hzero
    exact one_ne_zero hzero
  let u : Fin 3 → Kˣ := fun i => Units.mk0 (w i) (hne i)
  have hu : u 0 * u 1 * u 2 = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, Units.mk0_val]
    exact hdet
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  rw [← hcoe]
  rfl

theorem uc22pwI3_torus_action [Finite K] [CharP K 2]
    (ν : MulAut (SpecialLinearGroup (Fin 3) K))
    (hν : ∀ s, s ∈ unitriangular 3 K ↔ ν s ∈ unitriangular 3 K) :
    ∃ (i : ℕ) (ε : Bool), ∀ d ∈ SpecialLinearGroup.diagonalTorus K 3,
      ν d * (uc22pwI3TorusMap K ε i d)⁻¹ ∈ unitriangular 3 K := by
  obtain ⟨A, φ, ε, hε, hνeq⟩ := CFSG.Quasithin.H13.Ch4.KGSL3.exists_standard ν
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow φ
  have hpre : ∀ u₁ ∈ unitriangular 3 K, ν.symm u₁ ∈ unitriangular 3 K ∧ ν (ν.symm u₁) = u₁ := by
    intro u₁ hu₁
    have h2 : ν (ν.symm u₁) = u₁ := ν.apply_symm_apply u₁
    exact ⟨(hν (ν.symm u₁)).2 (by rw [h2]; exact hu₁), h2⟩
  have hAB : (A : Matrix (Fin 3) (Fin 3) K) *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.mul_inv A
  have hBA : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (A : Matrix (Fin 3) (Fin 3) K) = 1 := Units.inv_mul A
  interval_cases ε
  · have hmat : ∀ s : SpecialLinearGroup (Fin 3) K,
        (ν s : Matrix (Fin 3) (Fin 3) K) =
          (A : Matrix (Fin 3) (Fin 3) K) * (s : Matrix (Fin 3) (Fin 3) K).map φ *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro s
      rw [hνeq]
      exact uc22pwI3_matrix_zero A φ s
    have hAup : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
      refine uc22pwI3_upper_of_invariant _ _ hAB hBA (fun u₁ hu₁ => ?_)
      obtain ⟨hs, hs'⟩ := hpre u₁ hu₁
      refine ⟨((ν.symm u₁ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).map φ, ?_, ?_⟩
      · intro k l hkl
        simp [Matrix.map_apply, hs.1 k l hkl]
      · have h1 := hmat (ν.symm u₁)
        rw [hs'] at h1
        calc (u₁ : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)
            = ((A : Matrix (Fin 3) (Fin 3) K) *
              ((ν.symm u₁ : SpecialLinearGroup (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K).map φ *
                ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
                  (A : Matrix (Fin 3) (Fin 3) K) := by rw [← h1]
          _ = (A : Matrix (Fin 3) (Fin 3) K) *
              ((ν.symm u₁ : SpecialLinearGroup (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K).map φ := by
              rw [Matrix.mul_assoc, hBA, Matrix.mul_one]
    refine ⟨i, false, fun d hd => ?_⟩
    obtain ⟨v, hv⟩ := exists_uc22pwI3TorusHom_eq_of_mem_diagonalTorus hd
    have hdmat : (d : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (fun j => ((v.1 j : Kˣ) : K)) := by rw [← hv]; rfl
    have hDeq : (((d ^ 2 ^ i : SpecialLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (fun j => (((v.1 j : Kˣ) : K) ^ 2 ^ i)) := by
      rw [Matrix.SpecialLinearGroup.coe_pow, hdmat, Matrix.diagonal_pow]
      rfl
    have hDup : (((d ^ 2 ^ i : SpecialLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
      rw [hDeq]
      exact fun k l hkl => Matrix.diagonal_apply_ne _ (ne_of_gt hkl)
    have hmapd : (d : Matrix (Fin 3) (Fin 3) K).map φ =
        ((d ^ 2 ^ i : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hdmat, Matrix.diagonal_map (map_zero φ), hDeq]
      congr 1
      funext j
      exact hi _
    refine uc22pwI3_mem_unitriangular (A := (A : Matrix (Fin 3) (Fin 3) K))
      (B := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (D := ((d ^ 2 ^ i : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (D' := (((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) hAup hDup
      (coe_inv_isUpperTriangular (A := d ^ 2 ^ i) hDup) hAB
      (fun r => coe_inv_apply_self_of_isUpperTriangular (A := d ^ 2 ^ i) hDup r) ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, hmat d, hmapd]
    rfl
  · have hmat : ∀ s : SpecialLinearGroup (Fin 3) K,
        (ν s : Matrix (Fin 3) (Fin 3) K) =
          (A : Matrix (Fin 3) (Fin 3) K) *
            ((((s⁻¹ : SpecialLinearGroup (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K)ᵀ).map φ) *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro s
      rw [hνeq]
      exact uc22pwI3_matrix_one A φ s
    have hJJ : uc22pwI3J K * uc22pwI3J K = 1 := uc22pwI3J_mul_self
    have hAB' : ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) *
        (uc22pwI3J K * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (uc22pwI3J K), hJJ, Matrix.one_mul, hAB]
    have hBA' : (uc22pwI3J K * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((A⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K), hBA, Matrix.one_mul, hJJ]
    have hAup : ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K).IsUpperTriangular := by
      refine uc22pwI3_upper_of_invariant _ _ hAB' hBA' (fun u₁ hu₁ => ?_)
      obtain ⟨hs, hs'⟩ := hpre u₁ hu₁
      refine ⟨uc22pwI3J K * (((((ν.symm u₁)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)ᵀ).map φ) * uc22pwI3J K, ?_, ?_⟩
      · intro k l hkl
        rw [uc22pwI3J_conj]
        have hrev : (Fin.rev k) < Fin.rev l := Fin.rev_lt_rev.2 hkl
        have h0 := (inv_mem hs).1 (Fin.rev l) (Fin.rev k) hrev
        rw [Matrix.map_apply, Matrix.transpose_apply, h0, map_zero]
      · have h1 := hmat (ν.symm u₁)
        rw [hs'] at h1
        calc (u₁ : Matrix (Fin 3) (Fin 3) K) * ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K)
            = ((A : Matrix (Fin 3) (Fin 3) K) *
              (((((ν.symm u₁)⁻¹ : SpecialLinearGroup (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K)ᵀ).map φ) *
                ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
                  ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) := by rw [← h1]
          _ = ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) *
              (uc22pwI3J K * (((((ν.symm u₁)⁻¹ : SpecialLinearGroup (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K)ᵀ).map φ) * uc22pwI3J K) := by
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
                hBA, Matrix.one_mul, ← Matrix.mul_assoc (uc22pwI3J K), hJJ, Matrix.one_mul]
    refine ⟨i, true, fun d hd => ?_⟩
    obtain ⟨v, hv⟩ := exists_uc22pwI3TorusHom_eq_of_mem_diagonalTorus hd
    have hdmat : (d : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (fun j => ((v.1 j : Kˣ) : K)) := by rw [← hv]; rfl
    have hd_pow : d ^ 2 ^ i = uc22pwI3TorusHom K (v ^ 2 ^ i) := by
      rw [← hv, map_pow]
    have hinv_coe : ((d⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (fun j => (((v.1 j : Kˣ) : K)⁻¹)) := by
      rw [show d⁻¹ = uc22pwI3TorusHom K v⁻¹ by rw [← hv, map_inv]]
      have h1 : (uc22pwI3TorusHom K v⁻¹ : SpecialLinearGroup (Fin 3) K) =
          (uc22pwI3TorusHom K v)⁻¹ := map_inv (uc22pwI3TorusHom K) v
      rw [h1, uc22pwI3TorusHom_inv_coe]
      congr 1
      funext j
      exact Units.val_inv_eq_inv_val _
    have hD'eq : (((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (fun j => ((((v.1 j : Kˣ) : K) ^ 2 ^ i)⁻¹)) := by
      rw [show (d ^ 2 ^ i)⁻¹ = uc22pwI3TorusHom K ((v ^ 2 ^ i)⁻¹) by
        rw [hd_pow, map_inv]]
      have h1 : (uc22pwI3TorusHom K ((v ^ 2 ^ i)⁻¹) : SpecialLinearGroup (Fin 3) K) =
          (uc22pwI3TorusHom K (v ^ 2 ^ i))⁻¹ :=
        map_inv (uc22pwI3TorusHom K) (v ^ 2 ^ i)
      rw [h1, uc22pwI3TorusHom_inv_coe]
      simp [Pi.pow_apply, Units.val_pow_eq_pow_val]
    have hgraph : ((((d⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)ᵀ).map φ) =
        (((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) := by
      rw [hinv_coe, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero φ), hD'eq]
      congr 1
      funext j
      rw [hi, inv_pow]
    have hmatν : (ν d : Matrix (Fin 3) (Fin 3) K) =
        (A : Matrix (Fin 3) (Fin 3) K) *
          (((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hmat d, hgraph]
    have hDeq : (((d ^ 2 ^ i : SpecialLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (fun j => (((v.1 j : Kˣ) : K) ^ 2 ^ i)) := by
      have hpow : (uc22pwI3TorusHom K (v ^ 2 ^ i) : SpecialLinearGroup (Fin 3) K) =
          (uc22pwI3TorusHom K v) ^ 2 ^ i := map_pow (uc22pwI3TorusHom K) v (2 ^ i)
      rw [hd_pow, hpow, uc22pwI3TorusHom_pow_coe]
    have hDup : (((d ^ 2 ^ i : SpecialLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
      rw [hDeq]
      exact fun k l hkl => Matrix.diagonal_apply_ne _ (ne_of_gt hkl)
    have hXup : (uc22pwI3J K * (((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K).IsUpperTriangular := by
      intro a b hab
      rw [uc22pwI3J_conj, hD'eq]
      exact Matrix.diagonal_apply_ne _ (fun h => (ne_of_gt hab) (Fin.rev_injective h))
    have hXinvup : (uc22pwI3J K * ((d ^ 2 ^ i : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K).IsUpperTriangular := by
      intro a b hab
      rw [uc22pwI3J_conj, hDeq]
      exact Matrix.diagonal_apply_ne _ (fun h => (ne_of_gt hab) (Fin.rev_injective h))
    have hAdinv : (A : Matrix (Fin 3) (Fin 3) K) *
        (((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) *
          (uc22pwI3J K * (((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) *
          (uc22pwI3J K * ((A⁻¹ : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (uc22pwI3J K) (uc22pwI3J K)
          ((((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) * (uc22pwI3J K * (uc22pwI3J K *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))), hJJ, Matrix.one_mul,
        ← Matrix.mul_assoc (uc22pwI3J K) (uc22pwI3J K)
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hJJ, Matrix.one_mul]
    have hXinv : (uc22pwI3Jsl K * (d ^ 2 ^ i)⁻¹ * uc22pwI3Jsl K)⁻¹ =
        uc22pwI3Jsl K * (d ^ 2 ^ i) * uc22pwI3Jsl K := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
      have hJ : (uc22pwI3Jsl K)⁻¹ = uc22pwI3Jsl K :=
        inv_eq_of_mul_eq_one_right (uc22pwI3Jsl_mul_self (K := K))
      rw [hJ, inv_inv]
      group
    have hXs_coe : ((uc22pwI3Jsl K * (d ^ 2 ^ i)⁻¹ * uc22pwI3Jsl K :
        SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        uc22pwI3J K * (((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uc22pwI3Jsl]
    have hXinv_coe : (((uc22pwI3Jsl K * (d ^ 2 ^ i)⁻¹ * uc22pwI3Jsl K)⁻¹ :
        SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        uc22pwI3J K * ((d ^ 2 ^ i : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K := by
      rw [hXinv]
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uc22pwI3Jsl]
    refine uc22pwI3_mem_unitriangular
      (A := (A : Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K)
      (B := uc22pwI3J K * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (D := uc22pwI3J K * (((d ^ 2 ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K)
      (D' := uc22pwI3J K * ((d ^ 2 ^ i : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * uc22pwI3J K) hAup hXup hXinvup hAB'
      (fun r => by
        simp only [uc22pwI3J_conj]
        rw [mul_comm]
        exact coe_inv_apply_self_of_isUpperTriangular (A := d ^ 2 ^ i) hDup (Fin.rev r)) ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, hmatν]
    unfold uc22pwI3TorusMap
    simp only [Bool.true_eq, if_true]
    rw [hXinv_coe, hAdinv]

end CFSG.LocalAnalysis.UniquenessCase.UC22

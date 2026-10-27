module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

private def caGen_phi {m : ℕ} (a : Matrix (Fin 1) (Fin m) (ZMod 2))
    (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) : BlkIdx 1 m → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl j) => a 0 j
  | Sum.inr (Sum.inr k) => c 0 k

private def caGen_psi {m : ℕ} (b : Matrix (Fin m) (Fin 1) (ZMod 2))
    (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) : BlkIdx 1 m → ZMod 2
  | Sum.inl _ => c 0 0
  | Sum.inr (Sum.inl j) => b j 0
  | Sum.inr (Sum.inr _) => 0

private theorem caGen_uGL_eq_one_add_vecMulVec {m : ℕ}
    (a : Matrix (Fin 1) (Fin m) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    (uGL a 0 c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      1 + vecMulVec (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) (caGen_phi a c) := by
  ext x y
  rw [coe_uGL]
  rcases x with x | x | x <;> rcases y with y | y | y
  all_goals try fin_cases x
  all_goals try fin_cases y
  all_goals simp [uMat, blk, caGen_phi, vecMulVec, Pi.single_apply, Matrix.one_apply,
    Matrix.add_apply]

private theorem caGen_uGL_eq_one_add_vecMulVec_eC {m : ℕ}
    (b : Matrix (Fin m) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    (uGL 0 b c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      1 + vecMulVec (caGen_psi b c) (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) := by
  ext x y
  rw [coe_uGL]
  rcases x with x | x | x <;> rcases y with y | y | y
  all_goals try fin_cases x
  all_goals try fin_cases y
  all_goals simp [uMat, blk, caGen_psi, vecMulVec, Pi.single_apply, Matrix.one_apply,
    Matrix.add_apply]

private theorem caGen_mem_uOne_iff {m : ℕ} {g : GL (BlkIdx 1 m) (ZMod 2)} :
    g ∈ uOne m ↔ ∃ φ : BlkIdx 1 m → ZMod 2, φ (Sum.inl 0) = 0 ∧
      (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
        1 + vecMulVec (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) φ := by
  constructor
  · rintro ⟨a, c, rfl⟩
    exact ⟨caGen_phi a c, rfl, caGen_uGL_eq_one_add_vecMulVec a c⟩
  · rintro ⟨φ, hφ, hg⟩
    refine ⟨Matrix.of fun _ j => φ (Sum.inr (Sum.inl j)),
      Matrix.of fun _ _ => φ (Sum.inr (Sum.inr 0)), ?_⟩
    apply Units.ext
    rw [hg, caGen_uGL_eq_one_add_vecMulVec]
    congr 2
    funext x
    rcases x with x | x | x
    · fin_cases x
      simp [caGen_phi, hφ]
    · rfl
    · fin_cases x
      rfl

private theorem caGen_mem_uTwo_iff {m : ℕ} {g : GL (BlkIdx 1 m) (ZMod 2)} :
    g ∈ uTwo m ↔ ∃ ψ : BlkIdx 1 m → ZMod 2, ψ (Sum.inr (Sum.inr 0)) = 0 ∧
      (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
        1 + vecMulVec ψ (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) := by
  constructor
  · rintro ⟨b, c, rfl⟩
    exact ⟨caGen_psi b c, by simp [caGen_psi], caGen_uGL_eq_one_add_vecMulVec_eC b c⟩
  · rintro ⟨ψ, hψ, hg⟩
    refine ⟨Matrix.of fun j _ => ψ (Sum.inr (Sum.inl j)),
      Matrix.of fun _ _ => ψ (Sum.inl 0), ?_⟩
    apply Units.ext
    rw [hg, caGen_uGL_eq_one_add_vecMulVec_eC]
    congr 2
    funext x
    rcases x with x | x | x
    · fin_cases x
      rfl
    · rfl
    · fin_cases x
      simp [caGen_psi, hψ]

private theorem caGen_conj_vecMulVec {m : ℕ} (g : GL (BlkIdx 1 m) (ZMod 2))
    (v w : BlkIdx 1 m → ZMod 2) :
    (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * vecMulVec v w *
        ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      vecMulVec ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ v)
        (w ᵥ* ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private theorem caGen_conj_mem_uOne {m : ℕ} {g : GL (BlkIdx 1 m) (ZMod 2)}
    (hg : (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ
      (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) = Pi.single (Sum.inl 0 : BlkIdx 1 m) 1)
    {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uOne m) :
    g * u * g⁻¹ ∈ uOne m := by
  obtain ⟨φ, hφ, hmat⟩ := caGen_mem_uOne_iff.mp hu
  rw [caGen_mem_uOne_iff]
  let M : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) :=
    (g⁻¹ : GL (BlkIdx 1 m) (ZMod 2))
  have hM : M *ᵥ Pi.single (Sum.inl 0 : BlkIdx 1 m) 1 =
      Pi.single (Sum.inl 0 : BlkIdx 1 m) 1 := by
    have h := congrArg (fun x => M *ᵥ x) hg
    rw [Matrix.mulVec_mulVec] at h
    have hM1 : M * (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 := by
      rw [show M = ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) by rfl,
        ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hM1, Matrix.one_mulVec] at h
    exact h.symm
  refine ⟨φ ᵥ* M, ?_, ?_⟩
  · calc (φ ᵥ* M) (Sum.inl 0)
        = φ ⬝ᵥ M.col (Sum.inl 0) := Matrix.vecMul_apply ..
      _ = φ ⬝ᵥ (M *ᵥ Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) := by
            rw [Matrix.mulVec_single_one]
      _ = φ ⬝ᵥ (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) := by rw [hM]
      _ = φ (Sum.inl 0) := dotProduct_single_one ..
      _ = 0 := hφ
  · have hgm : (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * M = 1 := by
      rw [show M = ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) by rfl,
        ← Units.val_mul, mul_inv_cancel, Units.val_one]
    change ((g * u * g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      1 + vecMulVec (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) (φ ᵥ* M)
    calc ((g * u * g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))
        = (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
            (u : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * M := by simp [M]
      _ = (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
            (1 + vecMulVec (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) φ) * M := by
            rw [hmat]
      _ = ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * 1 +
            (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
              vecMulVec (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) φ) * M := by
            rw [Matrix.mul_add]
      _ = ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) +
            (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
              vecMulVec (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) φ) * M := by
            rw [Matrix.mul_one]
      _ = (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * M +
            (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
              vecMulVec (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) φ * M := by
            rw [Matrix.add_mul]
      _ = 1 + (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
              vecMulVec (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) φ * M := by
            rw [hgm]
      _ = 1 + vecMulVec
            ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ
              Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) (φ ᵥ* M) := by
            rw [caGen_conj_vecMulVec]
      _ = 1 + vecMulVec (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) (φ ᵥ* M) := by rw [hg]

private theorem caGen_conj_mem_uTwo {m : ℕ} {g : GL (BlkIdx 1 m) (ZMod 2)}
    (hg : (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) ᵥ*
      (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1)
    {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uTwo m) :
    g * u * g⁻¹ ∈ uTwo m := by
  obtain ⟨ψ, hψ, hmat⟩ := caGen_mem_uTwo_iff.mp hu
  rw [caGen_mem_uTwo_iff]
  let M : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) :=
    (g⁻¹ : GL (BlkIdx 1 m) (ZMod 2))
  have hgm : (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * M = 1 := by
    rw [show M = ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) by rfl,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hrowM : M.row (Sum.inr (Sum.inr 0)) =
      Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1 := by
    rw [← Matrix.single_one_vecMul]
    have h := congrArg (fun x => x ᵥ* M) hg
    rw [Matrix.vecMul_vecMul, hgm, Matrix.vecMul_one] at h
    exact h.symm
  have hrowg : (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).row
      (Sum.inr (Sum.inr 0)) = Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1 := by
    rw [← Matrix.single_one_vecMul]
    exact hg
  refine ⟨(g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ ψ, ?_, ?_⟩
  · calc ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ ψ)
          (Sum.inr (Sum.inr 0))
        = (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).row
            (Sum.inr (Sum.inr 0)) ⬝ᵥ ψ := Matrix.mulVec_apply ..
      _ = (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) ⬝ᵥ ψ := by rw [hrowg]
      _ = ψ (Sum.inr (Sum.inr 0)) := single_one_dotProduct ..
      _ = 0 := hψ
  · change ((g * u * g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      1 + vecMulVec ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ ψ)
        (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1)
    calc ((g * u * g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))
        = (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
            (u : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * M := by simp [M]
      _ = (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
            (1 + vecMulVec ψ (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1)) * M := by
            rw [hmat]
      _ = ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * 1 +
            (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
              vecMulVec ψ (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1)) * M := by
            rw [Matrix.mul_add]
      _ = ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) +
            (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
              vecMulVec ψ (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1)) * M := by
            rw [Matrix.mul_one]
      _ = (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * M +
            (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
              vecMulVec ψ (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) * M := by
            rw [Matrix.add_mul]
      _ = 1 + (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
              vecMulVec ψ (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) * M := by
            rw [hgm]
      _ = 1 + vecMulVec
            ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ ψ)
            (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1 ᵥ* M) := by
            rw [caGen_conj_vecMulVec]
      _ = 1 + vecMulVec
            ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ ψ)
            (M.row (Sum.inr (Sum.inr 0))) := by rw [Matrix.single_one_vecMul]
      _ = 1 + vecMulVec
            ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ ψ)
            (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) := by rw [hrowM]

private theorem caGen_inv_mulVec_eA {m : ℕ} {g : GL (BlkIdx 1 m) (ZMod 2)}
    (hg : (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ
      (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) = Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) :
    ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ
      (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) = Pi.single (Sum.inl 0 : BlkIdx 1 m) 1 := by
  have h := congrArg (fun x => ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
    Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x) hg
  rw [Matrix.mulVec_mulVec] at h
  have h1 : ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
      (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1, Matrix.one_mulVec] at h
  exact h.symm

private theorem caGen_inv_vecMul_eC {m : ℕ} {g : GL (BlkIdx 1 m) (ZMod 2)}
    (hg : (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) ᵥ*
      (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) :
    (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) ᵥ*
      ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1 := by
  have h := congrArg (fun x => x ᵥ* ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
    Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))) hg
  rw [Matrix.vecMul_vecMul] at h
  have h1 : (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
      ((g⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [h1, Matrix.vecMul_one] at h
  exact h.symm

private theorem caGen_mem_normalizer_uOne {m : ℕ} {g : GL (BlkIdx 1 m) (ZMod 2)}
    (hg : (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ
      (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) = Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) :
    g ∈ Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact caGen_conj_mem_uOne hg hu
  · intro hu
    have hg' := caGen_inv_mulVec_eA hg
    have h := caGen_conj_mem_uOne hg' hu
    simpa [mul_assoc] using h

private theorem caGen_mem_normalizer_uTwo {m : ℕ} {g : GL (BlkIdx 1 m) (ZMod 2)}
    (hg : (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) ᵥ*
      (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1) :
    g ∈ Subgroup.normalizer (uTwo m : Set (GL (BlkIdx 1 m) (ZMod 2))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact caGen_conj_mem_uTwo hg hu
  · intro hu
    have hg' := caGen_inv_vecMul_eC hg
    have h := caGen_conj_mem_uTwo hg' hu
    simpa [mul_assoc] using h

private theorem caGen_transvectionUnit_mulVec_eA {m : ℕ} {i j : BlkIdx 1 m}
    (hij : i ≠ j) (hj : j ≠ Sum.inl 0) :
    (TauCeti.transvectionUnit hij (1 : ZMod 2) :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ
      (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1) =
      Pi.single (Sum.inl 0 : BlkIdx 1 m) 1 := by
  rw [TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  have h0 : (Pi.single (Sum.inl 0 : BlkIdx 1 m) 1 : BlkIdx 1 m → ZMod 2) j = 0 := by
    rw [Pi.single_eq_of_ne hj]
  rw [h0, mul_zero]
  simp

private theorem caGen_transvectionUnit_vecMul_eC {m : ℕ} {i j : BlkIdx 1 m}
    (hij : i ≠ j) (hi : i ≠ Sum.inr (Sum.inr 0)) :
    (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1 : BlkIdx 1 m → ZMod 2) ᵥ*
      (TauCeti.transvectionUnit hij (1 : ZMod 2) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1 := by
  rw [TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.vecMul_add,
    Matrix.vecMul_one]
  have hsingle : (Pi.single (Sum.inr (Sum.inr 0) : BlkIdx 1 m) 1 : BlkIdx 1 m → ZMod 2) ᵥ*
      (Matrix.single i j (1 : ZMod 2)) = 0 := by
    ext k
    simp [Matrix.vecMul_apply, Matrix.single_apply, Pi.single_apply, hi]
  rw [hsingle, add_zero]

private def caGen_toUnit {m : ℕ} (t : Matrix.TransvectionStruct (BlkIdx 1 m) (ZMod 2)) :
    GL (BlkIdx 1 m) (ZMod 2) :=
  TauCeti.transvectionUnit t.hij t.c

private theorem caGen_toUnit_coe {m : ℕ} (t : Matrix.TransvectionStruct (BlkIdx 1 m) (ZMod 2)) :
    (caGen_toUnit t : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = t.toMatrix := by
  obtain ⟨i, j, hij, c⟩ := t
  rw [caGen_toUnit, TauCeti.coe_transvectionUnit, Matrix.TransvectionStruct.toMatrix_mk]

private theorem caGen_toUnit_mem {m : ℕ} (t : Matrix.TransvectionStruct (BlkIdx 1 m) (ZMod 2)) :
    caGen_toUnit t ∈ Subgroup.closure {g : GL (BlkIdx 1 m) (ZMod 2) |
      ∃ (i j : BlkIdx 1 m) (hij : i ≠ j), g = TauCeti.transvectionUnit hij (1 : ZMod 2)} := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) t.c with hc | hc
  · rw [caGen_toUnit, hc, TauCeti.transvectionUnit_zero]
    exact Subgroup.one_mem _
  · rw [caGen_toUnit, hc]
    exact Subgroup.subset_closure ⟨t.i, t.j, t.hij, rfl⟩

private theorem caGen_closure_transvectionUnit_eq_top {m : ℕ} :
    Subgroup.closure {g : GL (BlkIdx 1 m) (ZMod 2) |
      ∃ (i j : BlkIdx 1 m) (hij : i ≠ j),
        g = TauCeti.transvectionUnit hij (1 : ZMod 2)} = ⊤ := by
  let S : Set (GL (BlkIdx 1 m) (ZMod 2)) := {g |
    ∃ (i j : BlkIdx 1 m) (hij : i ≠ j),
      g = TauCeti.transvectionUnit hij (1 : ZMod 2)}
  have hS : Subgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec
      (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))
    let P : GL (BlkIdx 1 m) (ZMod 2) := (L.map caGen_toUnit).prod
    let Q : GL (BlkIdx 1 m) (ZMod 2) := (L'.map caGen_toUnit).prod
    have hmap : ∀ (M : List (Matrix.TransvectionStruct (BlkIdx 1 m) (ZMod 2))),
        ((M.map caGen_toUnit).prod : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
          (M.map Matrix.TransvectionStruct.toMatrix).prod := by
      intro M
      induction M with
      | nil => simp
      | cons t M ih => simp [List.prod_cons, Units.val_mul, caGen_toUnit_coe, ih]
    have hPmat : (P : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
        (L.map Matrix.TransvectionStruct.toMatrix).prod := by
      simpa [P] using hmap L
    have hQmat : (Q : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
        (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
      simpa [Q] using hmap L'
    rw [← hPmat, ← hQmat] at hD
    have hPunit : IsUnit (P : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) :=
      ⟨P, rfl⟩
    have hQunit : IsUnit (Q : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) :=
      ⟨Q, rfl⟩
    have hgunit : IsUnit (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) :=
      ⟨g, rfl⟩
    have hPdet : IsUnit ((P : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).det) :=
      (Matrix.isUnit_iff_isUnit_det _).mp hPunit
    have hQdet : IsUnit ((Q : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).det) :=
      (Matrix.isUnit_iff_isUnit_det _).mp hQunit
    have hgdet : IsUnit ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).det) :=
      (Matrix.isUnit_iff_isUnit_det _).mp hgunit
    have hdet_eq : (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).det =
        ((P : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).det *
          (Matrix.diagonal D).det) *
          (Q : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).det := by
      rw [hD, Matrix.det_mul, Matrix.det_mul]
    have hprod : IsUnit (((P : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).det *
        (Matrix.diagonal D).det) *
        (Q : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).det) := by
      rw [← hdet_eq]
      exact hgdet
    have hDdet : IsUnit (Matrix.diagonal D).det := by
      exact (IsUnit.mul_left_iff hPdet).mp ((IsUnit.mul_right_iff hQdet).mp hprod)
    rw [Matrix.det_diagonal] at hDdet
    have hD1 : ∀ i, D i = 1 := by
      intro i
      have hi : IsUnit (D i) := (IsUnit.prod_univ_iff.mp hDdet) i
      have hne : D i ≠ 0 := hi.ne_zero
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (D i) with h | h
      · exact absurd h hne
      · exact h
    have hdiag : Matrix.diagonal D = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.diagonal_apply, hD1 i]
      · simp [Matrix.diagonal_apply, hij, Matrix.one_apply, hij]
    have hg_eq : g = P * Q := by
      apply Units.ext
      rw [Units.val_mul, hD, hdiag, Matrix.mul_one]
    have hL : (L.map caGen_toUnit).prod ∈ Subgroup.closure S := by
      apply Subgroup.list_prod_mem
      intro u hu
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hu
      exact caGen_toUnit_mem t
    have hL' : (L'.map caGen_toUnit).prod ∈ Subgroup.closure S := by
      apply Subgroup.list_prod_mem
      intro u hu
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hu
      exact caGen_toUnit_mem t
    rw [hg_eq]
    exact Subgroup.mul_mem (Subgroup.closure S)
      (by simpa [P] using hL) (by simpa [Q] using hL')
  exact hS

theorem normalizer_uOne_sup_normalizer_uTwo {m : ℕ} (hm : 1 ≤ m) :
    Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2))) ⊔
      Subgroup.normalizer (uTwo m : Set (GL (BlkIdx 1 m) (ZMod 2))) = ⊤ := by
  let N : Subgroup (GL (BlkIdx 1 m) (ZMod 2)) :=
    Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2))) ⊔
      Subgroup.normalizer (uTwo m : Set (GL (BlkIdx 1 m) (ZMod 2)))
  let S : Set (GL (BlkIdx 1 m) (ZMod 2)) := {g |
    ∃ (i j : BlkIdx 1 m) (hij : i ≠ j),
      g = TauCeti.transvectionUnit hij (1 : ZMod 2)}
  have hgen : Subgroup.closure S = ⊤ := caGen_closure_transvectionUnit_eq_top
  have hle : Subgroup.closure S ≤ N := by
    rw [Subgroup.closure_le]
    rintro g ⟨i, j, hij, rfl⟩
    by_cases hj : j = Sum.inl 0
    · by_cases hi : i = Sum.inr (Sum.inr 0)
      · subst hj
        subst hi
        let B : BlkIdx 1 m := Sum.inr (Sum.inl ⟨0, hm⟩)
        have hCB : (Sum.inr (Sum.inr 0) : BlkIdx 1 m) ≠ B := by simp [B]
        have hBA : B ≠ (Sum.inl 0 : BlkIdx 1 m) := by simp [B]
        have hCA : (Sum.inr (Sum.inr 0) : BlkIdx 1 m) ≠ (Sum.inl 0 : BlkIdx 1 m) :=
          Sum.inr_ne_inl
        have hx : TauCeti.transvectionUnit hCB (1 : ZMod 2) ∈
            Subgroup.normalizer (uOne m : Set (GL (BlkIdx 1 m) (ZMod 2))) := by
          exact caGen_mem_normalizer_uOne
            (caGen_transvectionUnit_mulVec_eA hCB (by simp [B]))
        have hy : TauCeti.transvectionUnit hBA (1 : ZMod 2) ∈
            Subgroup.normalizer (uTwo m : Set (GL (BlkIdx 1 m) (ZMod 2))) := by
          exact caGen_mem_normalizer_uTwo
            (caGen_transvectionUnit_vecMul_eC hBA (by simp [B]))
        have hij_eq : hij = hCA := Subsingleton.elim _ _
        have hcomm := TauCeti.commutatorElement_transvectionUnit hCB hBA hCA
          (1 : ZMod 2) (1 : ZMod 2)
        rw [mul_one] at hcomm
        rw [hij_eq, ← hcomm]
        exact Subgroup.mul_mem N
          (Subgroup.mul_mem N
            (Subgroup.mul_mem N (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy))
            (N.inv_mem (Subgroup.mem_sup_left hx)))
          (N.inv_mem (Subgroup.mem_sup_right hy))
      · apply Subgroup.mem_sup_right
        exact caGen_mem_normalizer_uTwo (caGen_transvectionUnit_vecMul_eC hij hi)
    · apply Subgroup.mem_sup_left
      exact caGen_mem_normalizer_uOne (caGen_transvectionUnit_mulVec_eA hij hj)
  have htop : (⊤ : Subgroup (GL (BlkIdx 1 m) (ZMod 2))) ≤ N := by
    rw [← hgen]
    exact hle
  exact top_le_iff.mp htop

end CFSG.StandardType.FF81.CentA

end

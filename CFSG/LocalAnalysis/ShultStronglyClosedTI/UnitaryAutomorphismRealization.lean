module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHyperbolic

public section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem map_mul_ringEquiv {l m n : Type} [Fintype m] (σ : K ≃+* K) (M : Matrix l m K)
    (N : Matrix m n K) : (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := (σ : K →+* K))

theorem map_one_ringEquiv {n : Type} [DecidableEq n] (σ : K ≃+* K) :
    (1 : Matrix n n K).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

theorem map_bar_map_comm {m n : Type} (h : UnitaryFieldData p f K) (σ : K ≃+* K)
    (M : Matrix m n K) : (M.map σ).map h.bar = (M.map h.bar).map σ := by
  ext i j
  simp [map_bar_comm]

theorem transpose_map_bar_transportInv (h : UnitaryFieldData p f K)
    (R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K) :
    ((transportInv h R).map h.bar)ᵀ = R * hypGram r ε K := by
  have hRR : (R.map h.bar).map h.bar = R := by
    ext i j
    simp [UnitaryFieldData.bar_bar]
  rw [transportInv, Matrix.map_mul, hypGram_map, transpose_map, hRR, transpose_mul,
    transpose_transpose, hypGram_transpose]

variable {h : UnitaryFieldData p f K} {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}

theorem map_transportInv_mul_map (hR : IsHypTransport h R) (σ : K ≃+* K) :
    (transportInv h R).map σ * R.map σ = 1 := by
  rw [← map_mul_ringEquiv, transportInv_mul hR, map_one_ringEquiv]

theorem map_transportInv_mul_map_assoc (hR : IsHypTransport h R) (σ : K ≃+* K) {n : Type}
    (X : Matrix (HypIndex r ε) n K) : (transportInv h R).map σ * (R.map σ * X) = X := by
  rw [← Matrix.mul_assoc, map_transportInv_mul_map hR, Matrix.one_mul]

theorem map_mul_map_transportInv (hR : IsHypTransport h R) (σ : K ≃+* K) :
    R.map σ * (transportInv h R).map σ = 1 := by
  rw [← map_mul_ringEquiv, mul_transportInv hR, map_one_ringEquiv]

@[expose] noncomputable def semiTransportGL (hR : IsHypTransport h R) (B : GL (HypIndex r ε) K)
    (σ : K ≃+* K) : GL (Fin (2 * r + ε)) K where
  val := R * (B : Matrix (HypIndex r ε) (HypIndex r ε) K) * (transportInv h R).map σ
  inv := R.map σ * ((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
    transportInv h R
  val_inv := by
    calc R * (B : Matrix (HypIndex r ε) (HypIndex r ε) K) * (transportInv h R).map σ *
          (R.map σ * ((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            transportInv h R)
        = R * ((B : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            ((transportInv h R).map σ * R.map σ) *
            ((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) *
            transportInv h R := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [map_transportInv_mul_map hR, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.mul_one, mul_transportInv hR]
  inv_val := by
    calc R.map σ * ((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          transportInv h R *
          (R * (B : Matrix (HypIndex r ε) (HypIndex r ε) K) * (transportInv h R).map σ)
        = R.map σ * (((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (transportInv h R * R) * (B : Matrix (HypIndex r ε) (HypIndex r ε) K)) *
            (transportInv h R).map σ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [transportInv_mul hR, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one, map_mul_map_transportInv hR]

theorem coe_semiTransportGL (hR : IsHypTransport h R) (B : GL (HypIndex r ε) K) (σ : K ≃+* K) :
    ((semiTransportGL hR B σ : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
      R * (B : Matrix (HypIndex r ε) (HypIndex r ε) K) * (transportInv h R).map σ :=
  rfl

theorem coe_semiTransportGL_inv (hR : IsHypTransport h R) (B : GL (HypIndex r ε) K)
    (σ : K ≃+* K) :
    (((semiTransportGL hR B σ)⁻¹ : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
      R.map σ * ((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        transportInv h R :=
  rfl

theorem semiTransportGL_unitary (hR : IsHypTransport h R) {B : GL (HypIndex r ε) K}
    (hB : ((B : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      (B : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K) (σ : K ≃+* K) :
    (((semiTransportGL hR B σ : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).map h.bar)ᵀ *
      (semiTransportGL hR B σ : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) = 1 := by
  have hinv : (((transportInv h R).map σ).map h.bar)ᵀ = R.map σ * hypGram r ε K := by
    rw [map_bar_map_comm, ← transpose_map, transpose_map_bar_transportInv, map_mul_ringEquiv,
      hypGram_map_ringEquiv]
  have hR' : (R.map h.bar)ᵀ * R = hypGram r ε K := hR
  rw [coe_semiTransportGL, Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul, hinv]
  calc R.map σ * hypGram r ε K *
        (((B : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * (R.map h.bar)ᵀ) *
        (R * (B : Matrix (HypIndex r ε) (HypIndex r ε) K) * (transportInv h R).map σ)
      = R.map σ * hypGram r ε K *
        (((B : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * ((R.map h.bar)ᵀ * R) *
          (B : Matrix (HypIndex r ε) (HypIndex r ε) K)) * (transportInv h R).map σ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hR', hB, Matrix.mul_assoc (R.map σ), hypGram_mul_self, Matrix.mul_one,
          map_mul_map_transportInv hR]

theorem transportGL_conj (hR : IsHypTransport h R) (B : GL (HypIndex r ε) K) (σ : K ≃+* K)
    (g : GL (HypIndex r ε) K) :
    transportGL hR (B * glAut σ g * B⁻¹) =
      semiTransportGL hR B σ * glAut σ (transportGL hR g) * (semiTransportGL hR B σ)⁻¹ := by
  apply Units.ext
  rw [coe_transportGL, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    coe_semiTransportGL, coe_semiTransportGL_inv, coe_glAut, coe_glAut, coe_transportGL,
    map_mul_ringEquiv, map_mul_ringEquiv]
  simp only [Matrix.mul_assoc, map_transportInv_mul_map_assoc hR]

theorem unitary_three_full_semilinear_automorphism_realization (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) (β : MulAut (unitaryPSU h 3)) :
    ∃ (σ : K ≃+* K) (A : GL (Fin 3) K),
      ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1 ∧
        ∀ g : unitarySU p f K 3,
          ∃ hg : A * glAut σ (g : GL (Fin 3) K) * A⁻¹ ∈ unitarySU p f K 3,
            β (unitaryProj h 3 g) = unitaryProj h 3 ⟨_, hg⟩ := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  set e := hypProjTransport h hR
  obtain ⟨σ, B, hB, hBg⟩ := exists_isometry_hypPSU h hq ((e.trans β).trans e.symm)
  refine ⟨σ, semiTransportGL hR B σ, semiTransportGL_unitary hR hB σ, fun g' => ?_⟩
  set g := (hypTransport h hR).symm g'
  have hg' : hypTransport h hR g = g' := MulEquiv.apply_symm_apply _ _
  obtain ⟨hg, hα⟩ := hBg g
  have hconj : transportGL hR (B * glAut σ (g : GL (HypIndex 1 1) K) * B⁻¹) =
      semiTransportGL hR B σ * glAut σ (g' : GL (Fin 3) K) * (semiTransportGL hR B σ)⁻¹ := by
    rw [transportGL_conj, ← hg']
    rfl
  have hmem := transportGL_mem hR ⟨_, hg⟩
  rw [hconj] at hmem
  refine ⟨hmem, ?_⟩
  have h1 : unitaryProj h 3 g' = e (hypProj h 1 1 g) := by
    rw [hypProjTransport_hypProj, hg']
  have h2 : e.symm (β (e (hypProj h 1 1 g))) = hypProj h 1 1 ⟨_, hg⟩ := hα
  rw [h1, ← e.apply_symm_apply (β (e (hypProj h 1 1 g))), h2, hypProjTransport_hypProj]
  congr 1
  exact Subtype.ext hconj

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3K
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IW
public import CFSG.Quasithin.Vol2.Ch11SecU1U3J

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KFBloom
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL)
open scoped MatrixGroups

@[expose] def uPlus (p : ℕ) : SL(2, ZMod p) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def uMinus (p : ℕ) : SL(2, ZMod p) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]

theorem map_adGL_uPlus (ι : ZMod p →+* K) :
    ((adGL (uPlus p) : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).map ι =
      adMat (1 : K) 1 0 1 := by
  rw [coe_adGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adMat, uPlus, map_ofNat ι 2]

theorem map_adGL_uMinus (ι : ZMod p →+* K) :
    ((adGL (uMinus p) : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).map ι =
      adMat (1 : K) 0 1 1 := by
  rw [coe_adGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adMat, uMinus, map_ofNat ι 2]

theorem trace_adMat_one (a b : K) (hab : a * b = 0) : (adMat (1 : K) a b 1).trace = 3 := by
  rw [Matrix.trace_fin_three]
  simp [adMat, hab]
  norm_num

theorem commute_conj {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {X : Matrix m m K} {Q : Matrix m n K} {Q' : Matrix n m K} {U : Matrix n n K} (hQ : Q' * Q = 1)
    (h : X * (Q * U * Q') = (Q * U * Q') * X) : (Q' * X * Q) * U = U * (Q' * X * Q) := by
  calc Q' * X * Q * U = Q' * X * Q * U * (Q' * Q) := by rw [hQ, Matrix.mul_one]
    _ = Q' * (X * (Q * U * Q')) * Q := by simp only [Matrix.mul_assoc]
    _ = Q' * ((Q * U * Q') * X) * Q := by rw [h]
    _ = (Q' * Q) * U * (Q' * X * Q) := by simp only [Matrix.mul_assoc]
    _ = U * (Q' * X * Q) := by rw [hQ, Matrix.one_mul]

omit [Fact p.Prime] in
theorem natCast_ne_zero_of_lt [CharP K p] {n : ℕ} (hn0 : 0 < n) (hn : n < p) : (n : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K p]
  intro hd
  have := Nat.le_of_dvd hn0 hd
  omega

theorem centralizer_map_commutator_eq_bot (h : UnitaryFieldData p 1 K) (hp5 : 5 ≤ p)
    {R : Matrix (Fin 3) (Fin 3) h.fixedField} (hRdet : R.det ≠ 0) (hRt : Rᵀ = R)
    {φ : isometrySL R →* hypPSU h 1 1} {Hm : Matrix (HypIndex 1 1) (Fin 3) K}
    {Wm : Matrix (Fin 3) (HypIndex 1 1) K} (hHW : Hm * Wm = 1) (hWH : Wm * Hm = 1)
    (hmat : ∀ g : isometrySL R, ∃ X : hypSU h 1 1, φ g = hypProj h 1 1 X ∧
        ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
          Hm * ((g : SL(3, h.fixedField)) : Matrix (Fin 3) (Fin 3) h.fixedField).map
            h.fixedField.subtype * Wm) :
    Subgroup.centralizer (((commutator ↥(isometrySL R)).map φ : Subgroup (hypPSU h 1 1)) :
      Set (hypPSU h 1 1)) = ⊥ := by
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have : Fintype h.fixedField := Fintype.ofFinite _
  have hcardF : Fintype.card h.fixedField = p := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField, pow_one]
  obtain ⟨g₀, hg₀⟩ := exists_omega_elements (ZMod.ringEquiv h.fixedField hcardF) hp5 hRt hRdet
  set e := ZMod.ringEquiv h.fixedField hcardF with he
  obtain ⟨ι, hι⟩ : ∃ ι : ZMod p →+* K, ι = h.fixedField.subtype.comp e.toRingHom := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀⟩ : ∃ G, G = (g₀ : Matrix (Fin 3) (Fin 3) (ZMod p)).map ι := ⟨_, rfl⟩
  obtain ⟨G₁, hG₁⟩ : ∃ G, G = ((g₀⁻¹ : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)).map ι := ⟨_, rfl⟩
  have hG01 : G₀ * G₁ = 1 := by
    rw [hG₀, hG₁, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hG10 : G₁ * G₀ = 1 := by
    rw [hG₀, hG₁, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hQQ' : (Hm * G₀) * (G₁ * Wm) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc G₀, hG01, Matrix.one_mul, hHW]
  have hQ'Q : (G₁ * Wm) * (Hm * G₀) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wm, hWH, Matrix.one_mul, hG10]
  have h2 : (2 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (K := K) (n := 2) (by norm_num) (by omega)
  have h3 : (3 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (K := K) (n := 3) (by norm_num) (by omega)
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨X, rfl⟩ := hypProj_surjective h 1 1 y
  have key : ∀ u : SL(2, ZMod p),
      (((adGL u : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).map ι).trace ≠ 0 →
      ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
          ((Hm * G₀) * ((adGL u : GL (Fin 3) (ZMod p)) :
            Matrix (Fin 3) (Fin 3) (ZMod p)).map ι * (G₁ * Wm)) =
        ((Hm * G₀) * ((adGL u : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)).map ι * (G₁ * Wm)) *
          ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
    intro u htr
    obtain ⟨w, hw, hwm⟩ := hg₀ u
    obtain ⟨Y, hY, hYm⟩ := hmat w
    have hM : (((g₀ * adGL u * g₀⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).map
        e.toRingHom).map h.fixedField.subtype = G₀ * ((adGL u : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)).map ι * G₁ := by
      rw [Matrix.map_map, ← RingHom.coe_comp, Units.val_mul, Units.val_mul, Matrix.map_mul,
        Matrix.map_mul, hG₀, hG₁, hι]
    have hYQ : ((Y : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
        (Hm * G₀) * ((adGL u : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)).map ι * (G₁ * Wm) := by
      rw [hYm, hwm, hM]
      simp only [Matrix.mul_assoc]
    have hc := Subgroup.mem_centralizer_iff.mp hy (φ w) ⟨w, hw, rfl⟩
    rw [hY, ← map_mul, ← map_mul] at hc
    have hk : (X * Y)⁻¹ * (Y * X) ∈ hypScalars h 1 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, hc, inv_mul_cancel]
    obtain ⟨c, -, -, hcs⟩ := hk
    have hYX : (Y : GL (HypIndex 1 1) K) * X =
        (X : GL (HypIndex 1 1) K) * Y * GeneralLinearGroup.scalar (HypIndex 1 1) c := by
      rw [← hcs]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hYXm := congrArg (fun g : GL (HypIndex 1 1) K =>
      (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) hYX
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one] at hYXm
    rw [hYQ] at hYXm
    have hXY : ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
        ((Hm * G₀) * ((adGL u : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)).map ι * (G₁ * Wm)) =
        (c : K)⁻¹ • (((Hm * G₀) * ((adGL u : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)).map ι * (G₁ * Wm)) *
            ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) := by
      rw [hYXm, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]
    have hXi : (((X : GL (HypIndex 1 1) K)⁻¹ : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
          ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have htrY : ((Hm * G₀) * ((adGL u : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)).map ι * (G₁ * Wm)).trace ≠ 0 := by
      rw [Matrix.trace_mul_cycle, hQ'Q, Matrix.one_mul]
      exact htr
    have hζ := eq_one_of_mul_eq_smul hXi hXY htrY
    rw [hζ, one_smul] at hXY
    exact hXY
  have hp' := commute_conj hQ'Q (key (uPlus p) (by
    rw [map_adGL_uPlus, trace_adMat_one 1 0 (mul_zero 1)]
    exact h3))
  have hm' := commute_conj hQ'Q (key (uMinus p) (by
    rw [map_adGL_uMinus, trace_adMat_one 0 1 (zero_mul 1)]
    exact h3))
  rw [map_adGL_uPlus] at hp'
  rw [map_adGL_uMinus] at hm'
  have hs := L3I.eq_scalar_of_commute_adMat h2 hp' hm'
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : K, ℓ = ((G₁ * Wm) * ((X : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) * (Hm * G₀)) 0 0 := ⟨_, rfl⟩
  rw [← hℓ] at hs
  apply hypProj_eq_one_of_scalar h (ℓ := ℓ)
  calc ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
      = (Hm * G₀) * ((G₁ * Wm) * ((X : GL (HypIndex 1 1) K) :
          Matrix (HypIndex 1 1) (HypIndex 1 1) K) * (Hm * G₀)) * (G₁ * Wm) := by
        rw [show (Hm * G₀) * ((G₁ * Wm) * ((X : GL (HypIndex 1 1) K) :
            Matrix (HypIndex 1 1) (HypIndex 1 1) K) * (Hm * G₀)) * (G₁ * Wm) =
            ((Hm * G₀) * (G₁ * Wm)) * ((X : GL (HypIndex 1 1) K) :
              Matrix (HypIndex 1 1) (HypIndex 1 1) K) * ((Hm * G₀) * (G₁ * Wm)) by
          simp only [Matrix.mul_assoc], hQQ', Matrix.one_mul, Matrix.mul_one]
    _ = _ := by
        rw [hs, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
          Matrix.mul_one, Matrix.smul_mul, hQQ', Matrix.smul_one_eq_diagonal]
        exact (Matrix.scalar_apply ℓ).symm

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3

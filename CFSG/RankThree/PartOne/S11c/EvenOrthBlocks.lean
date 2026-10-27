module

public import CFSG.RankThree.PartOne.S11c.BlockExt

import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne.HNRed

open Matrix

@[expose] def quad4 {K : Type*} [Field K] (a : Fin 4 → K) : K := a 0 * a 1 + a 2 * a 3

@[expose] def Lz : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0,0,0,1; 0,1,1,0; 0,1,0,0; 1,0,0,1]

@[expose] def Rz : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0,0,1,0; 0,1,0,1; 1,0,1,0; 0,1,0,0]

@[expose] def Cz : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]

@[expose] def c3z : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1]

@[expose] def g3z : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

theorem indep_z : ∀ u w : Fin 3, Lz ^ (u : ℕ) * Rz ^ (w : ℕ) = 1 → u = 0 ∧ w = 0 := by
  decide +kernel

@[expose] def Lu : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
  ⟨Lz, Lz * Lz, by decide +kernel, by decide +kernel⟩

@[expose] def Ru : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
  ⟨Rz, Rz * Rz, by decide +kernel, by decide +kernel⟩

@[expose] def Cu : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
  ⟨Cz, Cz, by decide +kernel, by decide +kernel⟩

@[expose] def c3u : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
  ⟨c3z, c3z, by decide +kernel, by decide +kernel⟩

@[expose] def g3u : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
  ⟨g3z, g3z, by decide +kernel, by decide +kernel⟩

theorem Lu_pow_three : Lu ^ 3 = 1 := by decide +kernel
theorem Ru_pow_three : Ru ^ 3 = 1 := by decide +kernel
theorem Lu_Ru_comm : Lu * Ru = Ru * Lu := by decide +kernel
theorem Cu_sq : Cu * Cu = 1 := by decide +kernel
theorem Cu_Lu : Cu * Lu * Cu⁻¹ = Lu⁻¹ := by decide +kernel
theorem Cu_Ru : Cu * Ru * Cu⁻¹ = Ru⁻¹ := by decide +kernel
theorem comm_c3u_g3u : c3u * g3u * c3u⁻¹ * g3u⁻¹ = Cu := by decide +kernel
theorem Cu_ne_one : Cu ≠ 1 := by decide +kernel

section CharTwo

variable (K : Type*) [Field K] [CharP K 2]

@[expose] def castM : Matrix (Fin 4) (Fin 4) (ZMod 2) →+* Matrix (Fin 4) (Fin 4) K :=
  (ZMod.castHom (dvd_refl 2) K).mapMatrix

@[expose] def castGL : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) →*
    Matrix.GeneralLinearGroup (Fin 4) K :=
  Units.map (castM K : Matrix (Fin 4) (Fin 4) (ZMod 2) →* Matrix (Fin 4) (Fin 4) K)

theorem castM_injective : Function.Injective (castM K) :=
  Matrix.map_injective (ZMod.castHom_injective K)

theorem castGL_injective : Function.Injective (castGL K) :=
  Units.map_injective fun _ _ h => castM_injective K h

@[expose] def Lg : Matrix.GeneralLinearGroup (Fin 4) K := castGL K Lu

@[expose] def Rg : Matrix.GeneralLinearGroup (Fin 4) K := castGL K Ru

@[expose] def Cg : Matrix.GeneralLinearGroup (Fin 4) K := castGL K Cu

@[expose] def c3g : Matrix.GeneralLinearGroup (Fin 4) K := castGL K c3u

@[expose] def g3g : Matrix.GeneralLinearGroup (Fin 4) K := castGL K g3u

theorem Lg_coe : ((Lg K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    castM K Lz := rfl
theorem Rg_coe : ((Rg K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    castM K Rz := rfl
theorem Cg_coe : ((Cg K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    castM K Cz := rfl
theorem c3g_coe : ((c3g K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    castM K c3z := rfl
theorem g3g_coe : ((g3g K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    castM K g3z := rfl

theorem Lg_pow_three : Lg K ^ 3 = 1 := by rw [Lg, ← map_pow, Lu_pow_three, map_one]
theorem Rg_pow_three : Rg K ^ 3 = 1 := by rw [Rg, ← map_pow, Ru_pow_three, map_one]
theorem Lg_Rg_comm : Lg K * Rg K = Rg K * Lg K := by
  rw [Lg, Rg, ← map_mul, ← map_mul, Lu_Ru_comm]
theorem Cg_sq : Cg K * Cg K = 1 := by rw [Cg, ← map_mul, Cu_sq, map_one]
theorem Cg_Lg : Cg K * Lg K * (Cg K)⁻¹ = (Lg K)⁻¹ := by
  simp only [Cg, Lg, ← map_inv, ← map_mul, Cu_Lu]
theorem Cg_Rg : Cg K * Rg K * (Cg K)⁻¹ = (Rg K)⁻¹ := by
  simp only [Cg, Rg, ← map_inv, ← map_mul, Cu_Ru]
theorem comm_c3g_g3g : c3g K * g3g K * (c3g K)⁻¹ * (g3g K)⁻¹ = Cg K := by
  simp only [c3g, g3g, Cg, ← map_inv, ← map_mul, comm_c3u_g3u]
theorem Cg_ne_one : Cg K ≠ 1 := fun h =>
  Cu_ne_one (castGL_injective K (h.trans (map_one _).symm))

theorem quad4_Lg (a : Fin 4 → K) :
    quad4 (((Lg K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ a) =
      quad4 a := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [Lg_coe]
  simp [quad4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, castM, Lz]
  linear_combination (a 1 * a 3) * h2

theorem quad4_Rg (a : Fin 4 → K) :
    quad4 (((Rg K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ a) =
      quad4 a := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [Rg_coe]
  simp [quad4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, castM, Rz]
  linear_combination (a 1 * a 2) * h2

theorem quad4_Cg (a : Fin 4 → K) :
    quad4 (((Cg K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ a) =
      quad4 a := by
  rw [Cg_coe]
  simp [quad4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, castM, Cz]
  ring

theorem quad4_c3g (a : Fin 4 → K) :
    quad4 (((c3g K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ a) =
      quad4 a := by
  rw [c3g_coe]
  simp [quad4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, castM, c3z]
  ring

theorem quad4_g3g (a : Fin 4 → K) :
    quad4 (((g3g K : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ a) =
      quad4 a := by
  rw [g3g_coe]
  simp [quad4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, castM, g3z]
  ring

end CharTwo

@[expose] def cubeHom2 {G : Type*} [Group G] (x y : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : Commute x y) : Multiplicative (ZMod 3 × ZMod 3) →* G where
  toFun a := x ^ (Multiplicative.toAdd a).1.val * y ^ (Multiplicative.toAdd a).2.val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy, pow_add, pow_add]
    calc x ^ (Multiplicative.toAdd a).1.val * x ^ (Multiplicative.toAdd b).1.val *
          (y ^ (Multiplicative.toAdd a).2.val * y ^ (Multiplicative.toAdd b).2.val) =
        x ^ (Multiplicative.toAdd a).1.val * (x ^ (Multiplicative.toAdd b).1.val *
          y ^ (Multiplicative.toAdd a).2.val) * y ^ (Multiplicative.toAdd b).2.val := by
          simp only [mul_assoc]
      _ = x ^ (Multiplicative.toAdd a).1.val * (y ^ (Multiplicative.toAdd a).2.val *
          x ^ (Multiplicative.toAdd b).1.val) * y ^ (Multiplicative.toAdd b).2.val := by
          rw [(hxy.pow_pow (Multiplicative.toAdd b).1.val (Multiplicative.toAdd a).2.val).eq]
      _ = _ := by simp only [mul_assoc]

theorem cubeHom2_pow_three {G : Type*} [Group G] (x y : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : Commute x y) (a : Multiplicative (ZMod 3 × ZMod 3)) :
    cubeHom2 x y hx hy hxy a ^ 3 = 1 := by
  rw [← map_pow]
  have h3 : ∀ u : ZMod 3, 3 * u = 0 := fun u => by
    have : (3 : ZMod 3) = 0 := by decide
    rw [this, zero_mul]
  have : a ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext
    · simpa using h3 (Multiplicative.toAdd a).1
    · simpa using h3 (Multiplicative.toAdd a).2
  rw [this, map_one]

section CharTwo2

variable (K : Type*) [Field K] [CharP K 2]

@[expose] def rho4 : Multiplicative (ZMod 3 × ZMod 3) →* Matrix.GeneralLinearGroup (Fin 4) K :=
  cubeHom2 (Lg K) (Rg K) (Lg_pow_three K) (Rg_pow_three K) (Lg_Rg_comm K)

theorem rho4_apply (a : Multiplicative (ZMod 3 × ZMod 3)) :
    rho4 K a = Lg K ^ (Multiplicative.toAdd a).1.val * Rg K ^ (Multiplicative.toAdd a).2.val :=
  rfl

theorem rho4_pow_three (a : Multiplicative (ZMod 3 × ZMod 3)) : rho4 K a ^ 3 = 1 :=
  cubeHom2_pow_three _ _ _ _ _ a

theorem rho4_conj (a : Multiplicative (ZMod 3 × ZMod 3)) :
    Cg K * rho4 K a * (Cg K)⁻¹ = (rho4 K a)⁻¹ := by
  have hL : MulAut.conj (Cg K) (Lg K) = (Lg K)⁻¹ := by rw [MulAut.conj_apply]; exact Cg_Lg K
  have hR : MulAut.conj (Cg K) (Rg K) = (Rg K)⁻¹ := by rw [MulAut.conj_apply]; exact Cg_Rg K
  have hcomm : Commute (Lg K) (Rg K) := Lg_Rg_comm K
  have h1 : MulAut.conj (Cg K) (rho4 K a) = (Lg K ^ (Multiplicative.toAdd a).1.val)⁻¹ *
      (Rg K ^ (Multiplicative.toAdd a).2.val)⁻¹ := by
    rw [rho4_apply, map_mul, map_pow, map_pow, hL, hR, inv_pow, inv_pow]
  rw [← MulAut.conj_apply, h1, rho4_apply, _root_.mul_inv_rev]
  exact ((hcomm.pow_pow _ _).inv_inv).eq

theorem rho4_injective : Function.Injective (rho4 K) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨⟨u, w⟩, rfl⟩ : ∃ p : ZMod 3 × ZMod 3, a = Multiplicative.ofAdd p := ⟨a.toAdd, rfl⟩
  have h1 : Lu ^ u.val * Ru ^ w.val = 1 := by
    apply castGL_injective K
    rw [map_mul, map_pow, map_pow, map_one]
    exact ha
  have h2 : Lz ^ u.val * Rz ^ w.val = 1 := by
    have := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) =>
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2))) h1
    simpa [Lu, Ru, Units.val_pow_eq_pow_val] using this
  obtain ⟨hu, hw⟩ := indep_z ⟨u.val, ZMod.val_lt u⟩ ⟨w.val, ZMod.val_lt w⟩ h2
  have hu0 : u.val = 0 := congrArg Fin.val hu
  have hw0 : w.val = 0 := congrArg Fin.val hw
  rw [ZMod.val_eq_zero] at hu0 hw0
  rw [hu0, hw0]
  rfl

end CharTwo2

end CFSG.RankThree.PartOne.HNRed

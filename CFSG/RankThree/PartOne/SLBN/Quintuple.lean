module

public import CFSG.RankThree.PartOne.SRC.ModelSp4Two

public section

namespace CFSG.RankThree.PartOne.SLBN

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.SRC
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

namespace Quintuple

def tabIdx : Fin 2 ⊕ Fin 2 → Fin 4 := Sum.elim ![0, 1] ![2, 3]

def tab (t : Fin 4 → Fin 4 → ℤ) (R : Type) [Ring R] :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.of fun i j => ((t (tabIdx i) (tabIdx j) : ℤ) : R)

theorem tab_map {R S : Type} [Ring R] [Ring S] (f : R →+* S) (t : Fin 4 → Fin 4 → ℤ) :
    (tab t R).map f = tab t S := by
  ext i j
  simp [tab]

def tJ : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 0, 1], ![-1, 0, 0, 0], ![0, -1, 0, 0]]

def tB : Fin 4 → Fin 4 → ℤ := ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, 1]]

def tNeg : Fin 4 → Fin 4 → ℤ := ![![-1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1]]

theorem tab_J (R : Type) [Ring R] : tab tJ R = fromBlocks 0 1 (-1) 0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [tab, tabIdx, tJ]

theorem tab_neg (R : Type) [Ring R] : tab tNeg R = Matrix.scalar (Fin 2 ⊕ Fin 2) (-1 : R) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [tab, tabIdx, tNeg, Matrix.scalar_apply]

theorem mat_longInv_eq {K : Type} [Field K] : mat 2 K (longInv K 2 0) = tab tB K := by
  rw [mat_longInv]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [tab, tabIdx, tB, mem_coords]

def tA2 : Fin 4 → Fin 4 → ℤ :=
  ![![0, 0, -1, -1], ![0, 0, -1, 1], ![-1, -1, 0, 0], ![-1, 1, 0, 0]]

def tAi2 : Fin 4 → Fin 4 → ℤ :=
  ![![0, 0, 1, 1], ![0, 0, 1, -1], ![1, 1, 0, 0], ![1, -1, 0, 0]]

def tA3 : Fin 4 → Fin 4 → ℤ :=
  ![![0, 1, 1, 0], ![1, 0, 0, 1], ![1, 0, 0, -1], ![0, 1, -1, 0]]

def tAi3 : Fin 4 → Fin 4 → ℤ :=
  ![![0, -1, -1, 0], ![-1, 0, 0, -1], ![-1, 0, 0, 1], ![0, -1, 1, 0]]

def tA4 : Fin 4 → Fin 4 → ℤ :=
  ![![1, 0, -1, 1], ![0, 1, 1, -1], ![1, 1, 1, 0], ![1, 1, 0, 1]]

def tAi4 : Fin 4 → Fin 4 → ℤ :=
  ![![1, 0, 1, -1], ![0, 1, -1, 1], ![-1, -1, 1, 0], ![-1, -1, 0, 1]]

def tA5 : Fin 4 → Fin 4 → ℤ :=
  ![![-1, -1, -1, 1], ![-1, -1, 1, -1], ![-1, 0, 0, 1], ![0, -1, 1, 0]]

def tAi5 : Fin 4 → Fin 4 → ℤ :=
  ![![0, 1, 1, -1], ![1, 0, -1, 1], ![1, 0, -1, -1], ![0, 1, -1, -1]]

variable {K : Type} [Field K] [CharP K 3]

theorem exists_spElt (t t' : Fin 4 → Fin 4 → ℤ)
    (h₁ : tab t (ZMod 3) * tab t' (ZMod 3) = 1) (h₂ : tab t' (ZMod 3) * tab t (ZMod 3) = 1)
    (hs : (tab t (ZMod 3))ᵀ * tab tJ (ZMod 3) * tab t (ZMod 3) = tab tJ (ZMod 3)) :
    ∃ G : StatedSp 2 K, mat 2 K G = tab t K ∧ mat 2 K G⁻¹ = tab t' K := by
  let φ : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  have e₁ : tab t K * tab t' K = 1 := by
    have := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) => M.map φ) h₁
    simpa only [Matrix.map_mul, tab_map, Matrix.map_one φ (map_zero φ) (map_one φ)] using this
  have e₂ : tab t' K * tab t K = 1 := by
    have := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) => M.map φ) h₂
    simpa only [Matrix.map_mul, tab_map, Matrix.map_one φ (map_zero φ) (map_one φ)] using this
  have es : (tab t K)ᵀ * fromBlocks 0 1 (-1) 0 * tab t K = fromBlocks 0 1 (-1) 0 := by
    have := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) => M.map φ) hs
    simp only [Matrix.map_mul, Matrix.transpose_map, tab_map] at this
    rwa [tab_J] at this
  exact ⟨⟨⟨tab t K, tab t' K, e₁, e₂⟩, Subgroup.subset_closure es⟩, rfl, rfl⟩

end Quintuple

open Quintuple

theorem exists_quintuple_psp4 {K : Type} [Field K] [CharP K 3] :
    ∃ g₂ g₃ g₄ g₅ : StatedProj (StatedSp 2 K),
      sp4Invol0 * (g₂ * sp4Invol0 * g₂⁻¹) * (g₃ * sp4Invol0 * g₃⁻¹) * (g₄ * sp4Invol0 * g₄⁻¹) *
        (g₅ * sp4Invol0 * g₅⁻¹) = 1 := by
  obtain ⟨G₂, h₂, h₂'⟩ := exists_spElt (K := K) tA2 tAi2 (by decide) (by decide) (by decide)
  obtain ⟨G₃, h₃, h₃'⟩ := exists_spElt (K := K) tA3 tAi3 (by decide) (by decide) (by decide)
  obtain ⟨G₄, h₄, h₄'⟩ := exists_spElt (K := K) tA4 tAi4 (by decide) (by decide) (by decide)
  obtain ⟨G₅, h₅, h₅'⟩ := exists_spElt (K := K) tA5 tAi5 (by decide) (by decide) (by decide)
  let φ : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  have hprod : tab tB (ZMod 3) * (tab tA2 (ZMod 3) * tab tB (ZMod 3) * tab tAi2 (ZMod 3)) *
      (tab tA3 (ZMod 3) * tab tB (ZMod 3) * tab tAi3 (ZMod 3)) *
      (tab tA4 (ZMod 3) * tab tB (ZMod 3) * tab tAi4 (ZMod 3)) *
      (tab tA5 (ZMod 3) * tab tB (ZMod 3) * tab tAi5 (ZMod 3)) = tab tNeg (ZMod 3) := by decide
  have hprodK : tab tB K * (tab tA2 K * tab tB K * tab tAi2 K) *
      (tab tA3 K * tab tB K * tab tAi3 K) * (tab tA4 K * tab tB K * tab tAi4 K) *
      (tab tA5 K * tab tB K * tab tAi5 K) = tab tNeg K := by
    have := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) => M.map φ) hprod
    simpa only [Matrix.map_mul, tab_map] using this
  have hmat : mat 2 K (longInv K 2 0 * (G₂ * longInv K 2 0 * G₂⁻¹) *
      (G₃ * longInv K 2 0 * G₃⁻¹) * (G₄ * longInv K 2 0 * G₄⁻¹) *
      (G₅ * longInv K 2 0 * G₅⁻¹)) = Matrix.scalar (Fin 2 ⊕ Fin 2) (-1 : K) := by
    simp only [map_mul, h₂, h₂', h₃, h₃', h₄, h₄', h₅, h₅', mat_longInv_eq, hprodK, tab_neg]
  refine ⟨QuotientGroup.mk' _ G₂, QuotientGroup.mk' _ G₃, QuotientGroup.mk' _ G₄,
    QuotientGroup.mk' _ G₅, ?_⟩
  rw [sp4Invol0]
  simp only [← map_inv, ← map_mul]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨-1, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one]
  exact hmat.symm

end CFSG.RankThree.PartOne.SLBN

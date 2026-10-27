module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeTrans
import CFSG.HardMathSupport.Malle.Proving.OuterHeisCoreFour
import CFSG.ClassicalGroups.Alternating.TransvectionGeneration
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup Matrix CFSG.LieType.SeitzGeneration

open CFSG.HardMathSupport.Malle.Proving
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

namespace L3Gen

open CFSG.HardMathSupport.Malle.Proving

variable {F : Type} [Field F]

def cSL (x y : F) (h : x ^ 3 + y ^ 3 = 1) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![x, 0, y; y, x, 0; 0, y, x], by
    simp [Matrix.det_fin_three]
    ring_nf
    exact h⟩

theorem shiftSL_mul_cSL (x y : F) (h : x ^ 3 + y ^ 3 = 1) :
    shiftSL * cSL x y h = cSL x y h * shiftSL := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cSL, shiftSL, Matrix.mul_apply, Fin.sum_univ_three]

def gMat (x y e : F) : Matrix (Fin 3) (Fin 3) F :=
  !![(x ^ 3 * e ^ 3 + y ^ 3) * (e⁻¹) ^ 3,
      (x * y ^ 2 * e ^ 3 - x * y ^ 2) * (e⁻¹) ^ 3,
      -x ^ 2 * y * e ^ 3 + x ^ 2 * y;
     0, x ^ 3 + y ^ 3, 0;
     (-x * y ^ 2 * e ^ 3 + x * y ^ 2) * (e⁻¹) ^ 3,
      (x ^ 2 * y * e ^ 3 - x ^ 2 * y) * (e⁻¹) ^ 3,
      y ^ 3 * e ^ 3 + x ^ 3]

theorem coe_cSL_mul_diagSL_mul_inv_mul_inv (x y e : F) (hxy : x ^ 3 + y ^ 3 = 1)
    (hd : e * e * (e⁻¹) ^ 2 = 1) :
    ((cSL x y hxy * diagSL e e ((e⁻¹) ^ 2) hd * (cSL x y hxy)⁻¹ *
      (diagSL e e ((e⁻¹) ^ 2) hd)⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = gMat x y e := by
  have he : e ≠ 0 := by rintro rfl; simp at hd
  change ((cSL x y hxy).1 * (diagSL e e ((e⁻¹) ^ 2) hd).1 *
          adjugate (cSL x y hxy).1 * adjugate (diagSL e e ((e⁻¹) ^ 2) hd).1 :
          Matrix (Fin 3) (Fin 3) F) = gMat x y e
  dsimp only [cSL, diagSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp [he] <;> try ring_nf <;> try simp

def dSL (e : F) (h : e * e * (e⁻¹) ^ 2 = 1) : SpecialLinearGroup (Fin 3) F :=
  diagSL e e ((e⁻¹) ^ 2) h

def tSL (e : F) (h : e * (e⁻¹) ^ 2 * e = 1) : SpecialLinearGroup (Fin 3) F :=
  diagSL e ((e⁻¹) ^ 2) e h

def uMat (a b : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, a, 0; 0, 1, 0; 0, b, 1]

def uSL (a b : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨uMat a b, by simp [uMat, Matrix.det_fin_three]⟩

def alpha (x y e : F) : F := x * y ^ 2 * (e ^ 3 - 1) ^ 2 * (e⁻¹) ^ 3

def beta (x y e : F) : F := x ^ 2 * y * (e ^ 3 - 1) ^ 2 * (e⁻¹) ^ 3

def tMat (e : F) : Matrix (Fin 3) (Fin 3) F :=
  !![e, 0, 0; 0, (e⁻¹) ^ 2, 0; 0, 0, e]

theorem uMat_mul_gMat_sub (x y e : F) (he : e ≠ 0) :
    uMat (alpha x y e) (beta x y e) * gMat x y e -
        tMat e * gMat x y e * adjugate (tMat e) =
      (x ^ 3 + y ^ 3 - 1) • !![0, alpha x y e, 0; 0, 0, 0; 0, beta x y e, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, gMat, tMat, alpha, beta, Matrix.adjugate_fin_three_of,
      Matrix.sub_apply, Matrix.smul_apply] <;>
    field_simp [he] <;> try ring_nf

theorem uSL_mul_g_eq (x y e : F) (hxy : x ^ 3 + y ^ 3 = 1)
    (hd : e * e * (e⁻¹) ^ 2 = 1) (ht : e * (e⁻¹) ^ 2 * e = 1) (he : e ≠ 0) :
    uSL (alpha x y e) (beta x y e) *
        (cSL x y hxy * dSL e hd * (cSL x y hxy)⁻¹ * (dSL e hd)⁻¹) =
      tSL e ht * (cSL x y hxy * dSL e hd * (cSL x y hxy)⁻¹ * (dSL e hd)⁻¹) *
        (tSL e ht)⁻¹ := by
  have hg : ((cSL x y hxy * dSL e hd * (cSL x y hxy)⁻¹ * (dSL e hd)⁻¹ :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = gMat x y e :=
    coe_cSL_mul_diagSL_mul_inv_mul_inv x y e hxy hd
  apply Subtype.ext
  change ((uSL (alpha x y e) (beta x y e)).1 *
      (cSL x y hxy * dSL e hd * (cSL x y hxy)⁻¹ * (dSL e hd)⁻¹).1 :
      Matrix (Fin 3) (Fin 3) F) =
    (tSL e ht).1 * (cSL x y hxy * dSL e hd * (cSL x y hxy)⁻¹ * (dSL e hd)⁻¹).1 *
      adjugate (tSL e ht).1
  rw [show (cSL x y hxy * dSL e hd * (cSL x y hxy)⁻¹ * (dSL e hd)⁻¹).1 =
    gMat x y e from hg]
  have h0 : uMat (alpha x y e) (beta x y e) * gMat x y e -
      tMat e * gMat x y e * adjugate (tMat e) = 0 := by
    have h := uMat_mul_gMat_sub x y e he
    rw [hxy] at h
    simpa using h
  have hu : (uSL (alpha x y e) (beta x y e)).1 = uMat (alpha x y e) (beta x y e) := rfl
  have ht' : (tSL e ht).1 = tMat e := rfl
  rw [hu, ht']
  exact sub_eq_zero.mp h0

theorem coe_shiftSL_mul_uSL_mul_inv (a b : F) :
    ((shiftSL * uSL a b * (shiftSL)⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
    1 + Matrix.vecMulVec ![b, a, 0] ![0, 0, 1] := by
  change (((shiftSL : SpecialLinearGroup (Fin 3) F)).1 * (uSL a b).1 *
      adjugate ((shiftSL : SpecialLinearGroup (Fin 3) F)).1 :
      Matrix (Fin 3) (Fin 3) F) = 1 + Matrix.vecMulVec ![b, a, 0] ![0, 0, 1]
  dsimp only [shiftSL, uSL, uMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

end L3Gen

theorem eq_top_of_diagSL_mem_of_centralizer_le {F : Type} [Field F] [Finite F]
    (hq : Nat.card F % 3 = 2) (hq5 : 5 ≤ Nat.card F)
    {H : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ H)
    (hcen : centralizer ({shiftSL} : Set (SpecialLinearGroup (Fin 3) F)) ≤ H) : H = ⊤ := by
  obtain ⟨y, hy0, hy1⟩ :=
    CFSG.ClassicalGroups.Alternating.exists_ne_zero_ne_one_of_two_lt_card (K := F) (by omega)
  obtain ⟨x, hx3⟩ := (cube_bijective hq).2 (1 - y ^ 3)
  have hxy : x ^ 3 + y ^ 3 = 1 := by linear_combination hx3
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : (1 : F) - y ^ 3 = 0 := by simpa using hx3.symm
    exact hy1 (cube_eq_one_imp hq (by linear_combination -h1))
  obtain ⟨e, he0, he1⟩ :=
    CFSG.ClassicalGroups.Alternating.exists_ne_zero_ne_one_of_two_lt_card (K := F) (by omega)
  have he3 : e ^ 3 ≠ 1 := fun h =>
    he1 (cube_eq_one_imp hq h)
  have hd : e * e * (e⁻¹) ^ 2 = 1 := by field_simp [he0]
  have ht : e * (e⁻¹) ^ 2 * e = 1 := by field_simp [he0]
  set c : SpecialLinearGroup (Fin 3) F := L3Gen.cSL x y hxy
  set d : SpecialLinearGroup (Fin 3) F := L3Gen.dSL e hd
  set t : SpecialLinearGroup (Fin 3) F := L3Gen.tSL e ht
  set g : SpecialLinearGroup (Fin 3) F := c * d * c⁻¹ * d⁻¹
  set u : SpecialLinearGroup (Fin 3) F := t * g * t⁻¹ * g⁻¹
  have hshiftH : (shiftSL : SpecialLinearGroup (Fin 3) F) ∈ H := by
    refine hcen ?_
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rfl
  have hcH : c ∈ H := by
    refine hcen ?_
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact L3Gen.shiftSL_mul_cSL x y hxy
  have hdH : d ∈ H := hdiag e e ((e⁻¹) ^ 2) hd
  have htH : t ∈ H := hdiag e ((e⁻¹) ^ 2) e ht
  have hgH : g ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hcH hdH) (H.inv_mem hcH)) (H.inv_mem hdH)
  have huH : u ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem htH hgH) (H.inv_mem htH)) (H.inv_mem hgH)
  have hg_eq : ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      L3Gen.gMat x y e := by
    simpa only [g, c, d, L3Gen.dSL] using
      L3Gen.coe_cSL_mul_diagSL_mul_inv_mul_inv x y e hxy hd
  have huSL : L3Gen.uSL (L3Gen.alpha x y e) (L3Gen.beta x y e) = u := by
    rw [show u = t * g * t⁻¹ * g⁻¹ from rfl, eq_mul_inv_iff_mul_eq]
    simpa only [c, d, t, g, L3Gen.dSL, L3Gen.tSL] using
      L3Gen.uSL_mul_g_eq x y e hxy hd ht he0
  have hα0 : L3Gen.alpha x y e ≠ 0 := by
    simp [L3Gen.alpha, hx0, hy0, he0, sub_ne_zero.mpr he3]
  have hβ0 : L3Gen.beta x y e ≠ 0 := by
    simp [L3Gen.beta, hx0, hy0, he0, sub_ne_zero.mpr he3]
  have huSLH : L3Gen.uSL (L3Gen.alpha x y e) (L3Gen.beta x y e) ∈ H := by
    rw [huSL]
    exact huH
  have hT : ((shiftSL * L3Gen.uSL (L3Gen.alpha x y e) (L3Gen.beta x y e) *
      (shiftSL)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + Matrix.vecMulVec ![L3Gen.beta x y e, L3Gen.alpha x y e, 0] ![0, 0, 1] :=
    L3Gen.coe_shiftSL_mul_uSL_mul_inv (L3Gen.alpha x y e) (L3Gen.beta x y e)
  have hTK : (shiftSL * L3Gen.uSL (L3Gen.alpha x y e) (L3Gen.beta x y e) *
      (shiftSL)⁻¹ : SpecialLinearGroup (Fin 3) F) ∈ H :=
    H.mul_mem (H.mul_mem hshiftH huSLH) (H.inv_mem hshiftH)
  exact eq_top_of_torus_shift_transvection hdiag hshiftH he0 he3 hT (by simp) hβ0 hα0
    (by simp) hTK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

module

import CFSG.RankThree.Classical.SpIsometry
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp4Q8

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spForm spEnd spEnd_apply)
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull

section LeviComm

variable {r : ℕ} {F : Type} [Field F]

private lemma spForm_sub_add_eq_zero {w v : Fin r ⊕ Fin r → F} (hwv : spForm r F w v = 0) :
    spForm r F (w - v) (w + v) = 0 := by
  have hvw : spForm r F v w = 0 := by rw [SpSeitz.spForm_swap, hwv, neg_zero]
  have h1 : spForm r F (w - v) (w + v) =
      spForm r F w w + spForm r F w v - spForm r F v w - spForm r F v v := by
    simp only [map_add, map_sub, LinearMap.sub_apply]
    ring
  rw [h1, CFSG.RankThree.Classical.spForm_isAlt.self_eq_zero, hwv, hvw,
    CFSG.RankThree.Classical.spForm_isAlt.self_eq_zero]
  ring

theorem spEnd_shortRoot {w v : Fin r ⊕ Fin r → F} (hwv : spForm r F w v = 0) (s : F)
    (y : Fin r ⊕ Fin r → F) :
    spEnd (spTransvection (w + v) s * spTransvection (w - v) (-s)) y =
      y + (2 * s) • (spForm r F y w • v + spForm r F y v • w) := by
  have hvw : spForm r F v w = 0 := by rw [SpSeitz.spForm_swap, hwv, neg_zero]
  rw [spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, spEnd_spTransvection]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hwv, hvw,
    CFSG.RankThree.Classical.spForm_isAlt.self_eq_zero]
  module

theorem shortRoot_inv {w v : Fin r ⊕ Fin r → F} (hwv : spForm r F w v = 0) (s : F) :
    (spTransvection (w + v) s * spTransvection (w - v) (-s))⁻¹ =
      spTransvection (w + v) (-s) * spTransvection (w - v) s := by
  rw [_root_.mul_inv_rev, spTransvection_inv, spTransvection_inv, neg_neg]
  exact SpSeitz.commute_spTransvection_of_orth (spForm_sub_add_eq_zero hwv) s (-s)

theorem shortRoot_commutator {w v v' : Fin r ⊕ Fin r → F} (hwv : spForm r F w v = 0)
    (hwv' : spForm r F w v' = 0) (s t : F) :
    spTransvection (w + v) s * spTransvection (w - v) (-s) *
        (spTransvection (w + v') t * spTransvection (w - v') (-t)) *
        (spTransvection (w + v) s * spTransvection (w - v) (-s))⁻¹ *
        (spTransvection (w + v') t * spTransvection (w - v') (-t))⁻¹ =
      spTransvection w (-8 * s * t * spForm r F v v') := by
  apply CFSG.RankThree.Classical.spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection (w + v) s * spTransvection (w - v) (-s) *
        (spTransvection (w + v') t * spTransvection (w - v') (-t)) *
        (spTransvection (w + v) s * spTransvection (w - v) (-s))⁻¹ *
        (spTransvection (w + v') t * spTransvection (w - v') (-t))⁻¹) y =
      spEnd (spTransvection w (-8 * s * t * spForm r F v v')) y
  have hvw : spForm r F v w = 0 := by rw [SpSeitz.spForm_swap, hwv, neg_zero]
  have hvw' : spForm r F v' w = 0 := by rw [SpSeitz.spForm_swap, hwv', neg_zero]
  have hvv : spForm r F v' v = -spForm r F v v' := by rw [SpSeitz.spForm_swap]
  have hself : ∀ x : Fin r ⊕ Fin r → F, spForm r F x x = 0 :=
    CFSG.RankThree.Classical.spForm_isAlt.self_eq_zero
  have hA1 : ∀ z, spEnd (spTransvection (w + v) s * spTransvection (w - v) (-s)) z =
      z + (2 * s) • (spForm r F z w • v + spForm r F z v • w) :=
    fun z => spEnd_shortRoot hwv s z
  have hA2 : ∀ z, spEnd (spTransvection (w + v) (-s) * spTransvection (w - v) s) z =
      z + (2 * (-s)) • (spForm r F z w • v + spForm r F z v • w) := by
    intro z
    simpa only [neg_neg] using spEnd_shortRoot hwv (-s) z
  have hB1 : ∀ z, spEnd (spTransvection (w + v') t * spTransvection (w - v') (-t)) z =
      z + (2 * t) • (spForm r F z w • v' + spForm r F z v' • w) :=
    fun z => spEnd_shortRoot hwv' t z
  have hB2 : ∀ z, spEnd (spTransvection (w + v') (-t) * spTransvection (w - v') t) z =
      z + (2 * (-t)) • (spForm r F z w • v' + spForm r F z v' • w) := by
    intro z
    simpa only [neg_neg] using spEnd_shortRoot hwv' (-t) z
  rw [shortRoot_inv hwv, shortRoot_inv hwv']
  rw [spEnd_mul, spEnd_mul, spEnd_mul]
  simp only [Module.End.mul_apply]
  rw [hA1, hB1, hA2, hB2, spEnd_spTransvection]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hvw,
    hvw', hvv, hwv, hwv', hself, mul_zero, add_zero, mul_neg, neg_mul, neg_neg]
  module

theorem shortRoot_commute {X : Module.End F (Fin r ⊕ Fin r → F)}
    (hXadj : ∀ y z, spForm r F (X y) z = -spForm r F y (X z)) {lam : F}
    {w v : Fin r ⊕ Fin r → F} (hw : X w = lam • w) (hv : X v = -lam • v)
    (hwv : spForm r F w v = 0) (s : F) (y : Fin r ⊕ Fin r → F) :
    spEnd (spTransvection (w + v) s * spTransvection (w - v) (-s)) (X y) =
      X (spEnd (spTransvection (w + v) s * spTransvection (w - v) (-s)) y) := by
  rw [spEnd_shortRoot hwv, spEnd_shortRoot hwv]
  simp only [map_add, map_smul]
  rw [hXadj y w, hXadj y v, hw, hv]
  simp only [map_smul, smul_eq_mul, neg_mul, neg_neg]
  module

theorem exists_sp_fix_of_skew {Y : Module.End F (Fin r ⊕ Fin r → F)}
    (hYadj : ∀ y z, spForm r F (Y y) z = -spForm r F y (Y z)) {μ : F}
    (hYY : ∀ y, Y (Y y) = -μ • y) {u : Fin r ⊕ Fin r → F} (hu : spForm r F u (Y u) ≠ 0)
    {l k : F} (hlk : l * l + μ * (k * k) = 1) :
    ∃ g : StatedSp r F, (∀ y, spEnd g (Y y) = Y (spEnd g y)) ∧ spEnd g u = u ∧
      ∀ v, spForm r F v u = 0 → spForm r F v (Y u) = 0 → spEnd g v = l • v + k • Y v := by
  classical
  set Yu : Fin r ⊕ Fin r → F := Y u with hYu
  set κ : F := spForm r F u Yu with hκ
  have hκ0 : κ ≠ 0 := by rw [hκ]; exact hu
  have hYuYu : spForm r F Yu Yu = 0 :=
    CFSG.RankThree.Classical.spForm_isAlt.self_eq_zero Yu
  have hYu_u : spForm r F Yu u = -κ := by
    have h := SpSeitz.spForm_swap (r := r) (K := F) u Yu
    rwa [← hκ] at h
  let π : Module.End F (Fin r ⊕ Fin r → F) :=
    (κ⁻¹ : F) • ((LinearMap.flip (spForm r F) Yu).smulRight u -
      (LinearMap.flip (spForm r F) u).smulRight Yu)
  have hπ : ∀ y, π y = κ⁻¹ • (spForm r F y Yu • u - spForm r F y u • Yu) := by
    intro y
    simp only [π, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
      LinearMap.flip_apply]
  have hπu : π u = u := by
    rw [hπ u, CFSG.RankThree.Classical.spForm_isAlt.self_eq_zero, zero_smul, sub_zero, ← hκ,
      smul_smul, inv_mul_cancel₀ hκ0, one_smul]
  have hπYu : π Yu = Yu := by
    rw [hπ Yu, hYuYu, hYu_u, zero_smul, zero_sub, neg_smul, neg_neg, smul_smul,
      inv_mul_cancel₀ hκ0, one_smul]
  have hπadj : ∀ y z, spForm r F (π y) z = spForm r F y (π z) := by
    intro y z
    have h1 : spForm r F Yu z = -spForm r F z Yu := SpSeitz.spForm_swap (r := r) (K := F) z Yu
    have h2 : spForm r F u z = -spForm r F z u := SpSeitz.spForm_swap (r := r) (K := F) z u
    rw [hπ y, hπ z]
    simp only [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul,
      smul_sub, h1, h2]
    ring
  have hπ2 : ∀ y, π (π y) = π y := by
    intro y
    rw [hπ (π y)]
    rw [hπadj y Yu, hπYu, hπadj y u, hπu, hπ y]
  have hπY : ∀ y, π (Y y) = Y (π y) := by
    intro y
    rw [hπ (Y y), hπ y]
    have h1 : spForm r F (Y y) Yu = μ * spForm r F y u := by
      have h := hYadj y Yu
      rw [hYY u] at h
      simpa only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul,
        neg_mul, neg_neg] using h
    have h2 : spForm r F (Y y) u = -spForm r F y Yu := hYadj y u
    have hYR : Y (κ⁻¹ • (spForm r F y Yu • u - spForm r F y u • Yu)) =
        κ⁻¹ • (spForm r F y Yu • Yu - spForm r F y u • (-μ • u)) := by
      rw [map_smul, map_sub, map_smul, map_smul, ← hYu, hYY u]
    rw [h1, h2, hYR]
    simp only [smul_neg, neg_smul, smul_smul]
    module
  have hqY : ∀ z, Y ((1 - π) z) = (1 - π) (Y z) := by
    intro z
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← hπY z]
    rfl
  have hcross : ∀ y z, spForm r F (π y) ((1 - π) z) = 0 := by
    intro y z
    have h1 : spForm r F (π y) ((1 - π) z) =
        spForm r F (π y) z - spForm r F (π y) (π z) := by
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [h1, hπadj y z, hπadj y (π z), hπ2 z, sub_self]
  have hcrossY : ∀ y z, spForm r F (π y) (Y ((1 - π) z)) = 0 := by
    intro y z
    rw [hqY z]
    exact hcross y (Y z)
  have hcross2 : ∀ y z, spForm r F ((1 - π) y) (π z) = 0 := by
    intro y z
    rw [SpSeitz.spForm_swap (x := π z) (y := (1 - π) y), hcross z y, neg_zero]
  have hcrossY2 : ∀ y z, spForm r F (Y ((1 - π) y)) (π z) = 0 := by
    intro y z
    rw [hYadj, ← hπY z, hcross2 y (Y z), neg_zero]
  let A : Module.End F (Fin r ⊕ Fin r → F) :=
    l • (1 : Module.End F (Fin r ⊕ Fin r → F)) + k • Y
  have hAapp : ∀ z, A z = l • z + k • Y z := by
    intro z
    simp only [A, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  let G : Module.End F (Fin r ⊕ Fin r → F) := π + A * (1 - π)
  have hGdecomp : ∀ y, G y = π y + A ((1 - π) y) := by
    intro y
    simp only [G, LinearMap.add_apply, Module.End.mul_apply]
  have hAA : ∀ y z, spForm r F (A ((1 - π) y)) (A ((1 - π) z)) =
      spForm r F ((1 - π) y) ((1 - π) z) := by
    intro y z
    rw [hAapp, hAapp]
    have h1 : spForm r F ((1 - π) y) (Y ((1 - π) z)) =
        -spForm r F (Y ((1 - π) y)) ((1 - π) z) := by
      have h := hYadj ((1 - π) y) ((1 - π) z)
      rw [h, neg_neg]
    have h2 : spForm r F (Y ((1 - π) y)) (Y ((1 - π) z)) =
        μ * spForm r F ((1 - π) y) ((1 - π) z) := by
      have h := hYadj ((1 - π) y) (Y ((1 - π) z))
      rw [hYY ((1 - π) z)] at h
      simpa only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul,
        neg_mul, neg_neg] using h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [h1, h2]
    linear_combination (spForm r F ((1 - π) y) ((1 - π) z)) * hlk
  have hiso : ∀ y z, spForm r F (G y) (G z) = spForm r F y z := by
    intro y z
    have h1 : spForm r F (π y) (A ((1 - π) z)) = 0 := by
      rw [hAapp]
      simp only [map_add, map_smul, smul_eq_mul, hcross y z, hcrossY y z, mul_zero, add_zero]
    have h2 : spForm r F (A ((1 - π) y)) (π z) = 0 := by
      rw [hAapp]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hcross2 y z, hcrossY2 y z, mul_zero, add_zero]
    have hdecomp : spForm r F y z =
        spForm r F (π y) (π z) + spForm r F ((1 - π) y) ((1 - π) z) := by
      have hy : y = π y + (1 - π) y := by
        rw [LinearMap.sub_apply, Module.End.one_apply]
        abel
      have hz : z = π z + (1 - π) z := by
        rw [LinearMap.sub_apply, Module.End.one_apply]
        abel
      conv_lhs => rw [hy, hz]
      simp only [map_add, LinearMap.add_apply]
      rw [hcross y z, hcross2 y z]
      ring
    rw [hGdecomp y, hGdecomp z, hdecomp]
    simp only [map_add, LinearMap.add_apply]
    rw [h1, h2, hAA y z]
    ring
  have hGY : ∀ y, G (Y y) = Y (G y) := by
    intro y
    rw [hGdecomp (Y y), hGdecomp y, ← hqY y, hπY y, hAapp, hAapp, map_add, map_add,
      map_smul, map_smul]
  have hGu : G u = u := by
    rw [hGdecomp u]
    have hq_u : (1 - π) u = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, hπu, sub_self]
    rw [hq_u, hAapp, map_zero, smul_zero, smul_zero, add_zero, add_zero, hπu]
  have hGv : ∀ v, spForm r F v u = 0 → spForm r F v Yu = 0 →
      G v = l • v + k • Y v := by
    intro v hv hvu
    have hπv : π v = 0 := by
      rw [hπ v, hv, hvu, zero_smul, zero_smul, sub_self, smul_zero]
    rw [hGdecomp v, hπv]
    have hq_v : (1 - π) v = v := by
      rw [LinearMap.sub_apply, Module.End.one_apply, hπv, sub_zero]
    rw [hq_v, hAapp, zero_add]
  obtain ⟨g, hg⟩ := CFSG.RankThree.Classical.exists_sp_of_isometry hiso
  refine ⟨g, ?_, ?_, ?_⟩
  · intro y
    rw [hg]
    exact hGY y
  · rw [hg]
    exact hGu
  · intro v hv hvu
    rw [hg]
    exact hGv v hv hvu

end LeviComm

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter

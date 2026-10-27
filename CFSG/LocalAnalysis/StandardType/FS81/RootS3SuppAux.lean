module

public import CFSG.LargeExtraspecial.OrthoF2Pairs57
public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.OrthoF2Fixed
public import CFSG.LargeExtraspecial.OrthoF2SpRadical
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open scoped MatrixGroups
open Matrix

namespace CFSG.StandardType.FrameRoute.FS81.SuppAux

open CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalInvolution.WeakCT

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

lemma map_conj_map {G X : Type*} [Group G] [Group X] (φ : G →* X) (p : G)
    (P : Subgroup G) :
    (P.map (MulAut.conj p).toMonoidHom).map φ =
      (P.map φ).map (MulAut.conj (φ p)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨φ z, Subgroup.mem_map_of_mem φ hz, ?_⟩
    simp [MulAut.conj_apply]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨p * z * p⁻¹, Subgroup.mem_map_of_mem _ hz, ?_⟩
    simp [MulAut.conj_apply]

theorem center_SL3_two_eq_bot : Subgroup.center SL(3, ZMod 2) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have h1 : r = 1 := by
      have : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
      exact this r (by simpa using hr)
    subst h1
    apply Subtype.ext
    rw [← hA]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

def swapSL : SL(3, ZMod 2) :=
  ⟨CFSG.ClassicalInvolution.Phan.swapMat, CFSG.ClassicalInvolution.Phan.det_swapMat⟩

private def rotSL : SL(2, ZMod 2) :=
  ⟨CFSG.ClassicalInvolution.Phan.rotMat, CFSG.ClassicalInvolution.Phan.det_rotMat⟩

private def rotSLInv : SL(2, ZMod 2) :=
  ⟨CFSG.ClassicalInvolution.Phan.rotMatInv, by
    rw [Matrix.det_fin_two]
    simp [CFSG.ClassicalInvolution.Phan.rotMatInv]⟩

private theorem swapSL_mul_self : swapSL * swapSL = 1 := by
  apply Subtype.ext
  exact CFSG.ClassicalInvolution.Phan.swapMat_mul_self

private theorem swapSL_inv : swapSL⁻¹ = swapSL :=
  inv_eq_of_mul_eq_one_right swapSL_mul_self

theorem map_conj_swapSL_B12 :
    (B12 (ZMod 2)).map (MulAut.conj swapSL).toMonoidHom = B23 (ZMod 2) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [B12] at hy
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [B23]
    refine MonoidHom.mem_range.mpr ⟨rotSL * A * rotSLInv, ?_⟩
    have hconj : (MulEquiv.toMonoidHom (MulAut.conj swapSL))
        (blockSL (ZMod 2) 3 2 0 (by omega) A) =
        swapSL * blockSL (ZMod 2) 3 2 0 (by omega) A * swapSL := by
      change (MulAut.conj swapSL) (blockSL (ZMod 2) 3 2 0 (by omega) A) =
        swapSL * blockSL (ZMod 2) 3 2 0 (by omega) A * swapSL
      rw [MulAut.conj_apply, swapSL_inv]
    rw [hconj]
    apply Subtype.ext
    change CFSG.ClassicalInvolution.Phan.blockMat 3 1
        ((rotSL * A * rotSLInv : SL(2, ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
      CFSG.ClassicalInvolution.Phan.swapMat *
        CFSG.ClassicalInvolution.Phan.blockMat 3 0 (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
        CFSG.ClassicalInvolution.Phan.swapMat
    rw [← CFSG.ClassicalInvolution.Phan.embPair_zero_eq_blockMat,
      ← CFSG.ClassicalInvolution.Phan.embPair_two_eq_blockMat,
      CFSG.ClassicalInvolution.Phan.swapMat_mul_embPair_two]
    congr 1
  · intro hx
    rw [B23] at hx
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [B12]
    refine Subgroup.mem_map.mpr
      ⟨blockSL (ZMod 2) 3 2 0 (by omega) (rotSL * A * rotSLInv),
        ⟨rotSL * A * rotSLInv, rfl⟩, ?_⟩
    have hconj : (MulEquiv.toMonoidHom (MulAut.conj swapSL))
        (blockSL (ZMod 2) 3 2 0 (by omega) (rotSL * A * rotSLInv)) =
        swapSL * blockSL (ZMod 2) 3 2 0 (by omega) (rotSL * A * rotSLInv) * swapSL := by
      change (MulAut.conj swapSL) (blockSL (ZMod 2) 3 2 0 (by omega) (rotSL * A * rotSLInv)) =
        swapSL * blockSL (ZMod 2) 3 2 0 (by omega) (rotSL * A * rotSLInv) * swapSL
      rw [MulAut.conj_apply, swapSL_inv]
    rw [hconj]
    apply Subtype.ext
    change CFSG.ClassicalInvolution.Phan.swapMat *
        CFSG.ClassicalInvolution.Phan.blockMat 3 0
          ((rotSL * A * rotSLInv : SL(2, ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
        CFSG.ClassicalInvolution.Phan.swapMat =
      CFSG.ClassicalInvolution.Phan.blockMat 3 1 (A : Matrix (Fin 2) (Fin 2) (ZMod 2))
    rw [← CFSG.ClassicalInvolution.Phan.embPair_zero_eq_blockMat,
      ← CFSG.ClassicalInvolution.Phan.embPair_two_eq_blockMat,
      CFSG.ClassicalInvolution.Phan.swapMat_mul_embPair_two]
    congr 1
    have hrot : (CFSG.ClassicalInvolution.Phan.rotMat : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
        CFSG.ClassicalInvolution.Phan.rotMat = 1 := by decide
    have hrotInv : (CFSG.ClassicalInvolution.Phan.rotMatInv : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
        CFSG.ClassicalInvolution.Phan.rotMatInv = 1 := by decide
    have hcoeeq : ((rotSL * A * rotSLInv : SL(2, ZMod 2)) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) =
        CFSG.ClassicalInvolution.Phan.rotMat * (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
          CFSG.ClassicalInvolution.Phan.rotMatInv := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      rfl
    rw [hcoeeq]
    calc CFSG.ClassicalInvolution.Phan.rotMat *
          (CFSG.ClassicalInvolution.Phan.rotMat * (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
            CFSG.ClassicalInvolution.Phan.rotMatInv) *
          CFSG.ClassicalInvolution.Phan.rotMatInv =
        (CFSG.ClassicalInvolution.Phan.rotMat * CFSG.ClassicalInvolution.Phan.rotMat) *
          (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
          (CFSG.ClassicalInvolution.Phan.rotMatInv *
            CFSG.ClassicalInvolution.Phan.rotMatInv) := by noncomm_ring
      _ = (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by rw [hrot, hrotInv, one_mul, mul_one]

theorem map_conj_swapSL_B23 :
    (B23 (ZMod 2)).map (MulAut.conj swapSL).toMonoidHom = B12 (ZMod 2) := by
  have hcomp : (MulAut.conj swapSL).toMonoidHom.comp (MulAut.conj swapSL).toMonoidHom =
      MonoidHom.id (SL(3, ZMod 2)) := by
    apply MonoidHom.ext
    intro x
    change (MulAut.conj swapSL) ((MulAut.conj swapSL) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    simp only [swapSL_inv]
    calc swapSL * (swapSL * x * swapSL) * swapSL =
          (swapSL * swapSL) * x * (swapSL * swapSL) := by group
      _ = x := by rw [swapSL_mul_self]; group
  calc (B23 (ZMod 2)).map (MulAut.conj swapSL).toMonoidHom
      = ((B12 (ZMod 2)).map (MulAut.conj swapSL).toMonoidHom).map
          (MulAut.conj swapSL).toMonoidHom := by rw [map_conj_swapSL_B12]
    _ = (B12 (ZMod 2)).map ((MulAut.conj swapSL).toMonoidHom.comp
          (MulAut.conj swapSL).toMonoidHom) := by rw [Subgroup.map_map]
    _ = B12 (ZMod 2) := by rw [hcomp, Subgroup.map_id]

private def sl2U : SL(2, ZMod 2) := ⟨!![1,1;0,1], by decide⟩
private def sl2L : SL(2, ZMod 2) := ⟨!![1,0;1,1], by decide⟩
def sl3E01 : SL(3, ZMod 2) := blockSL (ZMod 2) 3 2 0 (by omega) sl2U
def sl3E10 : SL(3, ZMod 2) := blockSL (ZMod 2) 3 2 0 (by omega) sl2L
def sl3E21 : SL(3, ZMod 2) := blockSL (ZMod 2) 3 2 1 (by omega) sl2L
def sl3E12 : SL(3, ZMod 2) := blockSL (ZMod 2) 3 2 1 (by omega) sl2U

theorem sl3E01_mem_B12 : sl3E01 ∈ B12 (ZMod 2) := ⟨sl2U, rfl⟩
theorem sl3E10_mem_B12 : sl3E10 ∈ B12 (ZMod 2) := ⟨sl2L, rfl⟩
theorem sl3E21_mem_B23 : sl3E21 ∈ B23 (ZMod 2) := ⟨sl2L, rfl⟩
theorem sl3E12_mem_B23 : sl3E12 ∈ B23 (ZMod 2) := ⟨sl2U, rfl⟩

theorem sl3E01_sq : sl3E01 * sl3E01 = 1 := by decide
theorem sl3E12_sq : sl3E12 * sl3E12 = 1 := by decide
theorem sl3E01_ne_one : sl3E01 ≠ 1 := by decide
theorem sl3E12_ne_one : sl3E12 ≠ 1 := by decide
theorem sl3E21_ne_sl3E12 : sl3E21 ≠ sl3E12 := by decide
theorem sl3E01_ne_sl3E10 : sl3E01 ≠ sl3E10 := by decide
theorem sl3E01_comm_sl3E21 : sl3E01 * sl3E21 = sl3E21 * sl3E01 := by decide
theorem sl3E10_comm_sl3E12 : sl3E10 * sl3E12 = sl3E12 * sl3E10 := by decide

def cE01E12 : SL(3, ZMod 2) := ⟨!![0,0,1; 1,0,0; 0,1,0], by decide⟩
def cE10E12 : SL(3, ZMod 2) := ⟨!![0,0,1; 0,1,0; 1,0,0], by decide⟩
def cE10E01 : SL(3, ZMod 2) := ⟨!![0,1,0; 1,0,0; 0,0,1], by decide⟩
def cE12E01 : SL(3, ZMod 2) := ⟨!![0,1,0; 0,0,1; 1,0,0], by decide⟩
def cE21E12 : SL(3, ZMod 2) := ⟨!![1,0,0; 0,0,1; 0,1,0], by decide⟩
def cA1E12 : SL(3, ZMod 2) := ⟨!![1,0,1; 0,0,1; 0,1,0], by decide⟩
def cA1E01 : SL(3, ZMod 2) := ⟨!![0,0,1; 0,1,0; 1,0,1], by decide⟩
def cA2E01 : SL(3, ZMod 2) := ⟨!![0,1,0; 1,0,1; 0,0,1], by decide⟩

theorem conj_E01_E12 : cE01E12 * sl3E01 = sl3E12 * cE01E12 := by decide
theorem conj_E10_E12 : cE10E12 * sl3E10 = sl3E12 * cE10E12 := by decide
theorem conj_E10_E01 : cE10E01 * sl3E10 = sl3E01 * cE10E01 := by decide
theorem conj_E12_E01 : cE12E01 * sl3E12 = sl3E01 * cE12E01 := by decide
theorem conj_E21_E12 : cE21E12 * sl3E21 = sl3E12 * cE21E12 := by decide
theorem conj_E21_E01 : cE10E12 * sl3E21 = sl3E01 * cE10E12 := by decide
theorem conj_A1_E12 : cA1E12 * (sl3E01 * sl3E21) = sl3E12 * cA1E12 := by decide
theorem conj_A1_E01 : cA1E01 * (sl3E01 * sl3E21) = sl3E01 * cA1E01 := by decide
theorem conj_A2_E12 : cA1E01 * (sl3E10 * sl3E12) = sl3E12 * cA1E01 := by decide
theorem conj_A2_E01 : cA2E01 * (sl3E10 * sl3E12) = sl3E01 * cA2E01 := by decide

lemma isTypeA_image_of_mul_eq {W : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hW : W ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    {φ : SL(3, ZMod 2) →* (V ≃ₗ[ZMod 2] V)} (hφW : ∀ x, φ x ∈ W)
    {τ : SL(3, ZMod 2)} (hτ : IsTypeA q (φ τ) 2)
    {t g : SL(3, ZMod 2)} (hg : g * t = τ * g) :
    IsTypeA q (φ t) 2 := by
  have h : φ t = (φ g)⁻¹ * φ τ * (φ g) := by
    have h' := congrArg φ hg
    rw [map_mul, map_mul] at h'
    calc φ t = (φ g)⁻¹ * (φ g * φ t) := by group
      _ = (φ g)⁻¹ * (φ τ * φ g) := by rw [h']
      _ = (φ g)⁻¹ * φ τ * (φ g) := by group
  rw [h]
  simpa only [inv_inv] using isTypeA_conj hτ (inv_mem (hW (hφW g)))

lemma inf_commSpace_ne_bot_of_commute
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V}
    (hα : IsTypeA q α 2) (hβ : IsTypeA q β 2) (hαβ : IsTypeA q (α * β) 2)
    (hc : α * β = β * α) : commSpace α ⊓ commSpace β ≠ ⊥ := by
  intro hbot
  have horth : ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, QuadraticMap.polar q a b = 0 :=
    ((commute_iff_of_isTypeA hq hα hβ).mp hc).resolve_left fun hne => hne hbot
  have h4 := isTypeA_four_mul_of_inf_eq_bot hq hα hβ hbot horth
  have h2 := hαβ.2.2.2.1
  have h4' := h4.2.1.2.2.2.1
  omega

lemma exists_ne_zero_mem_inf_of_commute
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V}
    (hα : IsTypeA q α 2) (hβ : IsTypeA q β 2) (hαβ : IsTypeA q (α * β) 2)
    (hc : α * β = β * α) :
    ∃ u ∈ commSpace α ⊓ commSpace β, u ≠ 0 := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := commSpace α ⊓ commSpace β) (inf_commSpace_ne_bot_of_commute hq hα hβ hαβ hc)
  exact ⟨u, hu, hu0⟩


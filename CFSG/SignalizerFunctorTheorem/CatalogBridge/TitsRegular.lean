module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.TitsWords
public import CFSG.LieType.Ree.TitsGeneratorData
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeRee

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NonLocal CFSG.SignalizerFunctorTheorem.NonLocalExc
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SectionRank.TitsOrder CFSG.SectionRank.TitsGen CFSG.LieType.Simplicity

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

abbrev F4Vec : Type := Fin ReeTag.F4.tag.rank → ℤ

@[expose] def z1Reflect (v : F4Vec) : F4Vec :=
  [3, 0].foldl (fun v i => reflect ReeTag.F4.tag (ReeTag.F4.tag.idx i) v) v

theorem z1Reflect_0010 : z1Reflect (Pi.single (2 : Fin 4) 1) = ![0, 0, 1, 1] := by
  funext k
  fin_cases k <;> rfl

theorem z1Reflect_0100 : z1Reflect (Pi.single (1 : Fin 4) 1) = ![1, 1, 0, 0] := by
  funext k
  fin_cases k <;> rfl

theorem z1Reflect_0120 : z1Reflect (![0, 1, 2, 0] : F4Vec) = ![1, 1, 2, 2] := by
  funext k
  fin_cases k <;> rfl

theorem root_0120 : IsRoot ReeTag.F4.tag (![0, 1, 2, 0] : F4Vec) := by
  have h : reflect ReeTag.F4.tag (2 : Fin 4) (Pi.single (1 : Fin 4) 1) =
      (![0, 1, 2, 0] : F4Vec) := by
    funext k
    fin_cases k <;> rfl
  rw [← h]
  exact IsRoot.reflect _ (isRoot_single _ _)

theorem isRoot_z1Reflect {β : F4Vec} (hβ : IsRoot ReeTag.F4.tag β) :
    IsRoot ReeTag.F4.tag (z1Reflect β) :=
  IsRoot.reflect _ (IsRoot.reflect _ hβ)

theorem root_0011 : IsRoot ReeTag.F4.tag (![0, 0, 1, 1] : F4Vec) := by
  rw [← z1Reflect_0010]
  exact isRoot_z1Reflect (isRoot_single ReeTag.F4.tag (2 : Fin 4))

theorem root_1100 : IsRoot ReeTag.F4.tag (![1, 1, 0, 0] : F4Vec) := by
  rw [← z1Reflect_0100]
  exact isRoot_z1Reflect (isRoot_single ReeTag.F4.tag (1 : Fin 4))

theorem root_1122 : IsRoot ReeTag.F4.tag (![1, 1, 2, 2] : F4Vec) := by
  rw [← z1Reflect_0120]
  exact isRoot_z1Reflect root_0120

theorem ne_single_of {β : F4Vec} {i : Fin 4}
    (h : @Ne (Fin 4 → ℤ) β (Pi.single i 1)) : β ≠ (Pi.single i 1 : F4Vec) := h

theorem root_0120_ne_1 : (![0, 1, 2, 0] : F4Vec) ≠ Pi.single (1 : Fin 4) 1 :=
  ne_single_of (by decide)

theorem root_0120_ne_2 : (![0, 1, 2, 0] : F4Vec) ≠ Pi.single (2 : Fin 4) 1 :=
  ne_single_of (by decide)

theorem root_0011_ne_1 : (![0, 0, 1, 1] : F4Vec) ≠ Pi.single (1 : Fin 4) 1 :=
  ne_single_of (by decide)

theorem root_0011_ne_2 : (![0, 0, 1, 1] : F4Vec) ≠ Pi.single (2 : Fin 4) 1 :=
  ne_single_of (by decide)

theorem root_1100_ne_1 : (![1, 1, 0, 0] : F4Vec) ≠ Pi.single (1 : Fin 4) 1 :=
  ne_single_of (by decide)

theorem root_1100_ne_2 : (![1, 1, 0, 0] : F4Vec) ≠ Pi.single (2 : Fin 4) 1 :=
  ne_single_of (by decide)

theorem root_1122_ne_1 : (![1, 1, 2, 2] : F4Vec) ≠ Pi.single (1 : Fin 4) 1 :=
  ne_single_of (by decide)

theorem root_1122_ne_2 : (![1, 1, 2, 2] : F4Vec) ≠ Pi.single (2 : Fin 4) 1 :=
  ne_single_of (by decide)

theorem single_2_ne_1 : (Pi.single (2 : Fin 4) 1 : Fin 4 → ℤ) ≠ Pi.single (1 : Fin 4) 1 := by
  decide

theorem single_1_ne_2 : (Pi.single (1 : Fin 4) 1 : Fin 4 → ℤ) ≠ Pi.single (2 : Fin 4) 1 := by
  decide

section Base

variable {K : Type} [Field K]

@[expose] def titsY (K : Type) [Field K] : ModGL ReeTag.F4.tag K :=
  ReeTag.titsGen1 K * (ReeTag.titsGen2 K * ReeTag.titsGen1 K * (ReeTag.titsGen2 K)⁻¹)

theorem titsGen1_eq_pinnedX : ReeTag.titsGen1 K =
    pinnedX ReeTag.F4.tag K (Pi.single (2 : Fin 4) 1) 1 *
      pinnedX ReeTag.F4.tag K (Pi.single (1 : Fin 4) 1) 1 *
        pinnedX ReeTag.F4.tag K (![0, 1, 2, 0] : F4Vec) 1 := by
  rw [ReeTag.titsGen1, pinnedX_single ReeTag.F4.tag K (2 : Fin 4) 1,
    pinnedX_single ReeTag.F4.tag K (1 : Fin 4) 1]

theorem pinnedX_mem_posUnipotent {β : F4Vec} (hβ : IsRoot ReeTag.F4.tag β)
    (hpos : 0 < height β) (c : K) : pinnedX ReeTag.F4.tag K β c ∈ posUnipotent ReeTag.F4.tag K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot ReeTag.F4.tag α ∧ 0 < height α}) ⟨hβ, hpos⟩ c

end Base

section Weyl

variable
  {K : Type} [Field K]

theorem titsGen2_conj_pinnedX (h2 : (2 : K) = 0) {β : F4Vec} (hβ : IsRoot ReeTag.F4.tag β)
    (c : K) : ReeTag.titsGen2 K * pinnedX ReeTag.F4.tag K β c * (ReeTag.titsGen2 K)⁻¹ =
      pinnedX ReeTag.F4.tag K (z1Reflect β) c := by
  have e0 : ReeTag.F4.tag.idx 0 = (0 : Fin 4) := rfl
  have e3 : ReeTag.F4.tag.idx 3 = (3 : Fin 4) := rfl
  have := prod_weylElt_conj_pinnedX_of_two_eq_zero (τ := ReeTag.F4.tag) h2 [3, 0] hβ c
  simpa [z1Reflect, ReeTag.titsGen2, mul_assoc, e0, e3] using this

theorem titsGen2_conj_titsGen1 (h2 : (2 : K) = 0) :
    ReeTag.titsGen2 K * ReeTag.titsGen1 K * (ReeTag.titsGen2 K)⁻¹ =
      pinnedX ReeTag.F4.tag K (![0, 0, 1, 1] : F4Vec) 1 *
        pinnedX ReeTag.F4.tag K (![1, 1, 0, 0] : F4Vec) 1 *
          pinnedX ReeTag.F4.tag K (![1, 1, 2, 2] : F4Vec) 1 := by
  rw [titsGen1_eq_pinnedX]
  have e : ∀ A B C z : ModGL ReeTag.F4.tag K,
      z * (A * B * C) * z⁻¹ = (z * A * z⁻¹) * (z * B * z⁻¹) * (z * C * z⁻¹) := by
    intro A B C z
    group
  have hA := titsGen2_conj_pinnedX h2 (isRoot_single ReeTag.F4.tag (2 : Fin 4)) (1 : K)
  have hB := titsGen2_conj_pinnedX h2 (isRoot_single ReeTag.F4.tag (1 : Fin 4)) (1 : K)
  have hC := titsGen2_conj_pinnedX h2 root_0120 (1 : K)
  rw [z1Reflect_0010] at hA
  rw [z1Reflect_0100] at hB
  rw [z1Reflect_0120] at hC
  rw [e, hA, hB, hC]

theorem titsY_eq (h2 : (2 : K) = 0) : titsY K =
    (pinnedX ReeTag.F4.tag K (Pi.single (2 : Fin 4) 1) 1 *
      pinnedX ReeTag.F4.tag K (Pi.single (1 : Fin 4) 1) 1 *
        pinnedX ReeTag.F4.tag K (![0, 1, 2, 0] : F4Vec) 1) *
    (pinnedX ReeTag.F4.tag K (![0, 0, 1, 1] : F4Vec) 1 *
      pinnedX ReeTag.F4.tag K (![1, 1, 0, 0] : F4Vec) 1 *
        pinnedX ReeTag.F4.tag K (![1, 1, 2, 2] : F4Vec) 1) := by
  rw [titsY, titsGen2_conj_titsGen1 h2, titsGen1_eq_pinnedX]

theorem titsY_mem_posUnipotent (h2 : (2 : K) = 0) : titsY K ∈ posUnipotent ReeTag.F4.tag K := by
  rw [titsY_eq h2]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) (mul_mem (mul_mem ?_ ?_) ?_)
  · exact pinnedX_mem_posUnipotent (isRoot_single ReeTag.F4.tag (2 : Fin 4)) (by decide) 1
  · exact pinnedX_mem_posUnipotent (isRoot_single ReeTag.F4.tag (1 : Fin 4)) (by decide) 1
  · exact pinnedX_mem_posUnipotent root_0120 (by decide) 1
  · exact pinnedX_mem_posUnipotent root_0011 (by decide) 1
  · exact pinnedX_mem_posUnipotent root_1100 (by decide) 1
  · exact pinnedX_mem_posUnipotent root_1122 (by decide) 1

end Weyl

section Coord

variable
  {K : Type} [Field K]

theorem hasCoord_titsY_one (h2 : (2 : K) = 0) :
    HasCoord (τ := ReeTag.F4.tag) (K := K) (1 : Fin 4) (titsY K) 1 := by
  rw [titsY_eq h2]
  have hX2 : HasCoord (τ := ReeTag.F4.tag) (K := K) (1 : Fin 4)
      (pinnedX ReeTag.F4.tag K (Pi.single (2 : Fin 4) 1) 1) 0 :=
    hasCoord_pinnedX_of_ne (isRoot_single ReeTag.F4.tag (2 : Fin 4)) (by decide) single_2_ne_1 1
  have hX1 : HasCoord (τ := ReeTag.F4.tag) (K := K) (1 : Fin 4)
      (pinnedX ReeTag.F4.tag K (Pi.single (1 : Fin 4) 1) 1) 1 :=
    hasCoord_pinnedX_single (τ := ReeTag.F4.tag) (K := K) (1 : Fin 4) 1
  have hP : HasCoord (τ := ReeTag.F4.tag) (K := K) (1 : Fin 4)
      (pinnedX ReeTag.F4.tag K (![0, 1, 2, 0] : F4Vec) 1) 0 :=
    hasCoord_pinnedX_of_ne root_0120 (by decide) root_0120_ne_1 1
  have hA : HasCoord (τ := ReeTag.F4.tag) (K := K) (1 : Fin 4)
      (pinnedX ReeTag.F4.tag K (![0, 0, 1, 1] : F4Vec) 1) 0 :=
    hasCoord_pinnedX_of_ne root_0011 (by decide) root_0011_ne_1 1
  have hB : HasCoord (τ := ReeTag.F4.tag) (K := K) (1 : Fin 4)
      (pinnedX ReeTag.F4.tag K (![1, 1, 0, 0] : F4Vec) 1) 0 :=
    hasCoord_pinnedX_of_ne root_1100 (by decide) root_1100_ne_1 1
  have hC : HasCoord (τ := ReeTag.F4.tag) (K := K) (1 : Fin 4)
      (pinnedX ReeTag.F4.tag K (![1, 1, 2, 2] : F4Vec) 1) 0 :=
    hasCoord_pinnedX_of_ne root_1122 (by decide) root_1122_ne_1 1
  have := ((hX2.mul hX1).mul hP).mul ((hA.mul hB).mul hC)
  simpa using this

theorem hasCoord_titsY_two (h2 : (2 : K) = 0) :
    HasCoord (τ := ReeTag.F4.tag) (K := K) (2 : Fin 4) (titsY K) 1 := by
  rw [titsY_eq h2]
  have hX2 : HasCoord (τ := ReeTag.F4.tag) (K := K) (2 : Fin 4)
      (pinnedX ReeTag.F4.tag K (Pi.single (2 : Fin 4) 1) 1) 1 :=
    hasCoord_pinnedX_single (τ := ReeTag.F4.tag) (K := K) (2 : Fin 4) 1
  have hX1 : HasCoord (τ := ReeTag.F4.tag) (K := K) (2 : Fin 4)
      (pinnedX ReeTag.F4.tag K (Pi.single (1 : Fin 4) 1) 1) 0 :=
    hasCoord_pinnedX_of_ne (isRoot_single ReeTag.F4.tag (1 : Fin 4)) (by decide) single_1_ne_2 1
  have hP : HasCoord (τ := ReeTag.F4.tag) (K := K) (2 : Fin 4)
      (pinnedX ReeTag.F4.tag K (![0, 1, 2, 0] : F4Vec) 1) 0 :=
    hasCoord_pinnedX_of_ne root_0120 (by decide) root_0120_ne_2 1
  have hA : HasCoord (τ := ReeTag.F4.tag) (K := K) (2 : Fin 4)
      (pinnedX ReeTag.F4.tag K (![0, 0, 1, 1] : F4Vec) 1) 0 :=
    hasCoord_pinnedX_of_ne root_0011 (by decide) root_0011_ne_2 1
  have hB : HasCoord (τ := ReeTag.F4.tag) (K := K) (2 : Fin 4)
      (pinnedX ReeTag.F4.tag K (![1, 1, 0, 0] : F4Vec) 1) 0 :=
    hasCoord_pinnedX_of_ne root_1100 (by decide) root_1100_ne_2 1
  have hC : HasCoord (τ := ReeTag.F4.tag) (K := K) (2 : Fin 4)
      (pinnedX ReeTag.F4.tag K (![1, 1, 2, 2] : F4Vec) 1) 0 :=
    hasCoord_pinnedX_of_ne root_1122 (by decide) root_1122_ne_2 1
  have := ((hX2.mul hX1).mul hP).mul ((hA.mul hB).mul hC)
  simpa using this

@[expose] def titsRegular (K : Type) [Field K] (i : Fin ReeTag.F4.tag.rank) :
    ModGL ReeTag.F4.tag K :=
  if i.val = 0 ∨ i.val = 3 then ReeTag.titsGen0 K else titsY K

theorem titsRegular_mem_posUnipotent (h2 : (2 : K) = 0) (i : Fin ReeTag.F4.tag.rank) :
    titsRegular K i ∈ posUnipotent ReeTag.F4.tag K := by
  by_cases hi : i.val = 0 ∨ i.val = 3
  · simp only [titsRegular, hi, ↓reduceIte]
    exact mul_mem (CFSG.LieType.Chevalley.xUnit_mem_posUnipotent _ 1)
      (CFSG.LieType.Chevalley.xUnit_mem_posUnipotent _ 1)
  · simp only [titsRegular, hi, ↓reduceIte]
    exact titsY_mem_posUnipotent h2

theorem hasCoord_titsRegular (h2 : (2 : K) = 0) (i : Fin ReeTag.F4.tag.rank) :
    HasCoord i (titsRegular K i) 1 := by
  by_cases hi : i.val = 0 ∨ i.val = 3
  · simp only [titsRegular, hi, ↓reduceIte]
    exact hasCoord_xUnit_xUnit_one i hi
  · simp only [titsRegular, hi, ↓reduceIte]
    have h12 : i.val = 1 ∨ i.val = 2 := by
      have := i.2
      change i.val < 4 at this
      omega
    rcases h12 with h | h
    · have hi1 : i = (1 : Fin 4) := Fin.ext h
      rw [hi1]
      exact hasCoord_titsY_one h2
    · have hi2 : i = (2 : Fin 4) := Fin.ext h
      rw [hi2]
      exact hasCoord_titsY_two h2

end Coord

section Words

variable
  {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem gWordG_g0_eq : ((gWordG K [1] : reeFixed ReeTag.F4 K 0) : ModGL ReeTag.F4.tag K) =
    ReeTag.titsGen0 K := by
  simp [gWordG, gEltG, genG]
  rfl

theorem gWordG_y_eq (h2 : (2 : K) = 0) :
    ((gWordG K [2, 3, 2, -3] : reeFixed ReeTag.F4 K 0) : ModGL ReeTag.F4.tag K) = titsY K := by
  simp [gWordG, gEltG, genG]
  rw [ReeTag.coe_titsG1 K h2, ReeTag.coe_titsZ1 K]
  simp [titsY, mul_assoc]

theorem canonicalRep_longest_eq {w₀ : WeylGroup ReeTag.F4.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.F4.tag).length w ≤
      (coxeterSystem ReeTag.F4.tag).length w₀) :
    ((canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀ : ModGL ReeTag.F4.tag K)) =
      ((gWordG K [3, 4, 3, 4, 3, 4, 3, 4] : reeFixed ReeTag.F4 K 0) : ModGL ReeTag.F4.tag K) := by
  have hrev₀ : ReversesSigns w₀ := reversesSigns_of_forall_length_le hw₀
  have hrevl : ReversesSigns ((coxeterSystem ReeTag.F4.tag).wordProd ReeTag.F4.longWord) :=
    fun α hα hpos =>
      height_wordProd_smul_neg_of_negCheck ReeTag.F4.negCheck_longWord ⟨α, hα⟩ hpos
  have hw : (coxeterSystem ReeTag.F4.tag).wordProd ReeTag.F4.longWord = w₀ := hrevl.eq hrev₀
  rw [← hw, canonicalRep_wordProd ReeTag.F4.isReduced_longWord]
  simp [ReeTag.longWord, gWordG, gEltG, genG]
  rw [ReeTag.coe_titsZ1 K, ReeTag.coe_titsZ2 K]
  simp [ReeTag.titsGen2, ReeTag.titsGen3, mul_assoc]
  rfl

end Words

end CFSG.SignalizerFunctorTheorem.CatalogBridge

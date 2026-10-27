module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Floor
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.Quasithin.He11

open Matrix

section Matrix

variable {F : Type*} [Field F]

abbrev SL2 (F : Type*) [Field F] : Type _ := SpecialLinearGroup (Fin 2) F

@[expose] def uMat (t : F) : SL2 F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lMat (t : F) : SL2 F :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_mul_apply (g h : SL2 F) (i j : Fin 2) :
    ((g * h : SL2 F) : Matrix (Fin 2) (Fin 2) F) i j =
      (g : Matrix (Fin 2) (Fin 2) F) i 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 j +
        (g : Matrix (Fin 2) (Fin 2) F) i 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem uMat_00 (t : F) : (uMat t : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := rfl
@[simp] theorem uMat_01 (t : F) : (uMat t : Matrix (Fin 2) (Fin 2) F) 0 1 = t := rfl
@[simp] theorem uMat_10 (t : F) : (uMat t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl
@[simp] theorem uMat_11 (t : F) : (uMat t : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := rfl
@[simp] theorem lMat_00 (t : F) : (lMat t : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := rfl
@[simp] theorem lMat_01 (t : F) : (lMat t : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := rfl
@[simp] theorem lMat_10 (t : F) : (lMat t : Matrix (Fin 2) (Fin 2) F) 1 0 = t := rfl
@[simp] theorem lMat_11 (t : F) : (lMat t : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := rfl

theorem ext_SL2 {g h : SL2 F}
    (h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = (h : Matrix (Fin 2) (Fin 2) F) 0 1)
    (h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (h : Matrix (Fin 2) (Fin 2) F) 1 1) : g = h := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem uMat_add (s t : F) : uMat (s + t) = uMat s * uMat t := by
  apply ext_SL2 <;> simp [coe_mul_apply, add_comm]

theorem uMat_zero : uMat (0 : F) = 1 := by
  apply ext_SL2 <;> simp

theorem uMat_injective : Function.Injective (uMat : F → SL2 F) := by
  intro s t h
  have := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa using this

theorem eq_u_l_u {g : SL2 F} (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    g = uMat (((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) *
      lMat ((g : Matrix (Fin 2) (Fin 2) F) 1 0) *
      uMat (((g : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  apply ext_SL2 <;> simp [coe_mul_apply] <;> field_simp
  all_goals first
    | linear_combination hdet
    | linear_combination (-1 : F) * hdet
    | ring

theorem closure_u_l_eq_top :
    Subgroup.closure (Set.range (uMat (F := F)) ∪ Set.range (lMat (F := F))) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hu : ∀ t : F, uMat t ∈ Subgroup.closure (Set.range (uMat (F := F)) ∪ Set.range (lMat (F := F))) :=
    fun t => Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)
  have hl : ∀ t : F, lMat t ∈ Subgroup.closure (Set.range (uMat (F := F)) ∪ Set.range (lMat (F := F))) :=
    fun t => Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)
  have key : ∀ g : SL2 F, (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 →
      g ∈ Subgroup.closure (Set.range (uMat (F := F)) ∪ Set.range (lMat (F := F))) := by
    intro g hc
    rw [eq_u_l_u hc]
    exact mul_mem (mul_mem (hu _) (hl _)) (hu _)
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hdet := g.det_coe
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
    have hc' : ((lMat (1 : F) * g : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      simp [coe_mul_apply, hc, ha]
    have h1 := key _ hc'
    have : g = (lMat (1 : F))⁻¹ * (lMat 1 * g) := by group
    rw [this]
    exact mul_mem (inv_mem (hl 1)) h1
  · exact key g hc

end Matrix

section CharTwo

variable {F : Type*} [Field F] [CharP F 2]

@[expose] def wMat (c : F) (hc : c ≠ 0) : SL2 F :=
  ⟨!![0, c⁻¹; c, 0], by
    rw [Matrix.det_fin_two_of]
    have : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    rw [zero_mul, zero_sub, this, CharTwo.neg_eq]⟩

@[simp] theorem wMat_00 (c : F) (hc : c ≠ 0) : (wMat c hc : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := rfl
@[simp] theorem wMat_01 (c : F) (hc : c ≠ 0) : (wMat c hc : Matrix (Fin 2) (Fin 2) F) 0 1 = c⁻¹ := rfl
@[simp] theorem wMat_10 (c : F) (hc : c ≠ 0) : (wMat c hc : Matrix (Fin 2) (Fin 2) F) 1 0 = c := rfl
@[simp] theorem wMat_11 (c : F) (hc : c ≠ 0) : (wMat c hc : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := rfl

theorem uMat_mul_mul_uMat (h : SL2 F) (hc : (h : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    uMat ((h : Matrix (Fin 2) (Fin 2) F) 0 0 / (h : Matrix (Fin 2) (Fin 2) F) 1 0) * h *
      uMat ((h : Matrix (Fin 2) (Fin 2) F) 1 1 / (h : Matrix (Fin 2) (Fin 2) F) 1 0) =
    wMat ((h : Matrix (Fin 2) (Fin 2) F) 1 0) hc := by
  have hdet := h.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply ext_SL2 <;> simp [coe_mul_apply] <;> field_simp
  all_goals first
    | linear_combination ((h : Matrix (Fin 2) (Fin 2) F) 0 0) * h2
    | linear_combination ((h : Matrix (Fin 2) (Fin 2) F) 1 1) * h2
    | linear_combination hdet + ((h : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 1 1 +
        (h : Matrix (Fin 2) (Fin 2) F) 0 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 0) * h2

theorem wMat_mul_uMat (c : F) (hc : c ≠ 0) (t : F) :
    wMat c hc * uMat t = lMat (c ^ 2 * t) * wMat c hc := by
  apply ext_SL2 <;> simp [coe_mul_apply]
  field_simp

theorem lMat_mem_of_u_le {H : Subgroup (SL2 F)} (hU : ∀ t : F, uMat t ∈ H) {h : SL2 F} (hh : h ∈ H)
    (hc : (h : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) (s : F) : lMat s ∈ H := by
  set c : F := (h : Matrix (Fin 2) (Fin 2) F) 1 0 with hcdef
  have hw : wMat c hc ∈ H := by
    rw [← uMat_mul_mul_uMat h hc]
    exact mul_mem (mul_mem (hU _) hh) (hU _)
  have h1 : lMat (c ^ 2 * (s / c ^ 2)) = wMat c hc * uMat (s / c ^ 2) * (wMat c hc)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← wMat_mul_uMat]
  have h2 : c ^ 2 * (s / c ^ 2) = s := by field_simp
  rw [h2] at h1
  rw [h1]
  exact mul_mem (mul_mem hw (hU _)) (inv_mem hw)

theorem eq_top_of_u_le {H : Subgroup (SL2 F)} (hU : ∀ t : F, uMat t ∈ H) {h : SL2 F} (hh : h ∈ H)
    (hc : (h : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : H = ⊤ := by
  rw [eq_top_iff, ← closure_u_l_eq_top]
  refine (Subgroup.closure_le H).mpr ?_
  rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact hU t
  · exact lMat_mem_of_u_le hU hh hc t

end CharTwo

end CFSG.Quasithin.He11

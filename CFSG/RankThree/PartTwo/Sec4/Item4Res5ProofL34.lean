module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Res5L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable {k : Type*} [Field k]

@[expose] def uM (x y : k) : Matrix (Fin 3) (Fin 3) k := !![1, 0, x; 0, 1, y; 0, 0, 1]

theorem det_uM (x y : k) : (uM x y).det = 1 := by
  simp [uM, Matrix.det_fin_three]

@[expose] def uSL (x y : k) : Matrix.SpecialLinearGroup (Fin 3) k := ⟨uM x y, det_uM x y⟩

theorem coe_uSL (x y : k) : ((uSL x y : Matrix.SpecialLinearGroup (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k) = uM x y := rfl

theorem uSL_mul (x y x' y' : k) : uSL x y * uSL x' y' = uSL (x + x') (y + y') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_uSL, coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uSL_zero : uSL (0 : k) 0 = 1 := by
  apply Subtype.ext
  rw [coe_uSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM]

theorem uSL_inv (x y : k) : (uSL x y)⁻¹ = uSL (-x) (-y) := by
  rw [inv_eq_iff_mul_eq_one, uSL_mul, add_neg_cancel, add_neg_cancel, uSL_zero]

@[expose] def gM (a b c d : k) : Matrix (Fin 3) (Fin 3) k := !![a, b, 0; c, d, 0; 0, 0, 1]

theorem det_gM (a b c d : k) : (gM a b c d).det = a * d - b * c := by
  simp [gM, Matrix.det_fin_three]

@[expose] def gSL (a b c d : k) (h : a * d - b * c = 1) : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨gM a b c d, by rw [det_gM, h]⟩

theorem coe_gSL (a b c d : k) (h : a * d - b * c = 1) :
    ((gSL a b c d h : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      gM a b c d := rfl

theorem gSL_mul_uSL (a b c d : k) (h : a * d - b * c = 1) (x y : k) :
    gSL a b c d h * uSL x y = uSL (a * x + b * y) (c * x + d * y) * gSL a b c d h := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_gSL, coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM, gM, Matrix.mul_apply, Fin.sum_univ_three]

theorem gSL_inv (a b c d : k) (h : a * d - b * c = 1) :
    (gSL a b c d h)⁻¹ = gSL d (-b) (-c) a (by linear_combination h) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_gSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gM, Matrix.mul_apply, Fin.sum_univ_three]
    <;> first | linear_combination h | linear_combination -h | ring

variable (k) in
@[expose] def eOne : Subgroup (projectiveSL 3 k) where
  carrier := {g | ∃ x y : k, proj 3 k (uSL x y) = g}
  one_mem' := ⟨0, 0, by rw [uSL_zero, map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨x, y, rfl⟩ ⟨x', y', rfl⟩
    exact ⟨x + x', y + y', by rw [← map_mul, uSL_mul]⟩
  inv_mem' := by
    rintro _ ⟨x, y, rfl⟩
    exact ⟨-x, -y, by rw [← map_inv, uSL_inv]⟩

theorem proj_uSL_mem (x y : k) : proj 3 k (uSL x y) ∈ eOne k := ⟨x, y, rfl⟩

theorem eq_zero_of_proj_uSL_eq_one {x y : k} (h : proj 3 k (uSL x y) = 1) : x = 0 ∧ y = 0 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
  rw [coe_uSL] at hc
  have h02 := congrFun (congrFun hc 0) 2
  have h12 := congrFun (congrFun hc 1) 2
  simp [uM, scalar_apply] at h02 h12
  exact ⟨h02, h12⟩

theorem proj_uSL_injective {x y x' y' : k} (h : proj 3 k (uSL x y) = proj 3 k (uSL x' y')) :
    x = x' ∧ y = y' := by
  have h' : proj 3 k (uSL (x' - x) (y' - y)) = 1 := by
    rw [show uSL (x' - x) (y' - y) = (uSL x y)⁻¹ * uSL x' y' by
        rw [uSL_inv, uSL_mul, neg_add_eq_sub, neg_add_eq_sub], map_mul, map_inv, h,
      inv_mul_cancel]
  obtain ⟨h1, h2⟩ := eq_zero_of_proj_uSL_eq_one h'
  exact ⟨(sub_eq_zero.mp h1).symm, (sub_eq_zero.mp h2).symm⟩

theorem card_eOne [Finite k] : Nat.card (eOne k) = Nat.card k * Nat.card k := by
  have e : k × k ≃ eOne k :=
    Equiv.ofBijective (fun p => ⟨proj 3 k (uSL p.1 p.2), proj_uSL_mem _ _⟩) ⟨by
      rintro ⟨x, y⟩ ⟨x', y'⟩ h
      obtain ⟨h1, h2⟩ := proj_uSL_injective (congrArg Subtype.val h)
      exact Prod.ext h1 h2, by
      rintro ⟨_, ⟨x, y, rfl⟩⟩
      exact ⟨(x, y), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod]

theorem commute_of_mem_eOne {r s : projectiveSL 3 k} (hr : r ∈ eOne k) (hs : s ∈ eOne k) :
    r * s = s * r := by
  obtain ⟨x, y, rfl⟩ := hr
  obtain ⟨x', y', rfl⟩ := hs
  rw [← map_mul, ← map_mul, uSL_mul, uSL_mul, add_comm x, add_comm y]

theorem sq_eq_one_of_mem_eOne [CharP k 2] {r : projectiveSL 3 k} (hr : r ∈ eOne k) :
    r ^ 2 = 1 := by
  obtain ⟨x, y, rfl⟩ := hr
  rw [sq, ← map_mul, uSL_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, uSL_zero,
    map_one]

theorem proj_gSL_mem_normalizer (a b c d : k) (h : a * d - b * c = 1) :
    proj 3 k (gSL a b c d h) ∈ Subgroup.normalizer (eOne k : Set (projectiveSL 3 k)) := by
  have hfwd : ∀ (a b c d : k) (h : a * d - b * c = 1) (x y : k),
      proj 3 k (gSL a b c d h) * proj 3 k (uSL x y) * (proj 3 k (gSL a b c d h))⁻¹ ∈ eOne k := by
    intro a b c d h x y
    rw [← map_mul, gSL_mul_uSL, map_mul, mul_inv_cancel_right]
    exact proj_uSL_mem _ _
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, y, rfl⟩
    exact hfwd a b c d h x y
  · intro hg
    obtain ⟨x, y, hxy⟩ := hg
    have hinv : (proj 3 k (gSL a b c d h))⁻¹ =
        proj 3 k (gSL d (-b) (-c) a (by linear_combination h)) := by
      rw [← map_inv, gSL_inv]
    have hg' : g = (proj 3 k (gSL a b c d h))⁻¹ * proj 3 k (uSL x y) *
        ((proj 3 k (gSL a b c d h))⁻¹)⁻¹ := by
      rw [hxy]; group
    rw [hg', hinv]
    exact hfwd d (-b) (-c) a _ x y

theorem exists_conj_uSL_one_zero {x y : k} (hxy : ¬ (x = 0 ∧ y = 0)) :
    ∃ n ∈ Subgroup.normalizer (eOne k : Set (projectiveSL 3 k)),
      n * proj 3 k (uSL 1 0) * n⁻¹ = proj 3 k (uSL x y) := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := fun hy => hxy ⟨hx, hy⟩
    have h : (0 : k) * 0 - (-y⁻¹) * y = 1 := by field_simp; ring
    refine ⟨proj 3 k (gSL 0 (-y⁻¹) y 0 h), proj_gSL_mem_normalizer _ _ _ _ h, ?_⟩
    rw [← map_mul, gSL_mul_uSL, map_mul, mul_inv_cancel_right, hx]
    congr 2 <;> ring
  · have h : x * x⁻¹ - 0 * y = 1 := by field_simp; ring
    refine ⟨proj 3 k (gSL x 0 y x⁻¹ h), proj_gSL_mem_normalizer _ _ _ _ h, ?_⟩
    rw [← map_mul, gSL_mul_uSL, map_mul, mul_inv_cancel_right]
    congr 2 <;> ring

theorem exists_conj_eq_of_mem_eOne {r s : projectiveSL 3 k} (hr : r ∈ eOne k) (hs : s ∈ eOne k)
    (hr1 : r ≠ 1) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (eOne k : Set (projectiveSL 3 k)), n * r * n⁻¹ = s := by
  obtain ⟨x, y, rfl⟩ := hr
  obtain ⟨x', y', rfl⟩ := hs
  have h1 : ¬ (x = 0 ∧ y = 0) := by
    rintro ⟨rfl, rfl⟩; exact hr1 (by rw [uSL_zero, map_one])
  have h2 : ¬ (x' = 0 ∧ y' = 0) := by
    rintro ⟨rfl, rfl⟩; exact hs1 (by rw [uSL_zero, map_one])
  obtain ⟨n, hn, hnr⟩ := exists_conj_uSL_one_zero h1
  obtain ⟨m, hm, hms⟩ := exists_conj_uSL_one_zero h2
  refine ⟨m * n⁻¹, mul_mem hm (inv_mem hn), ?_⟩
  rw [← hms, ← hnr]
  group

end CFSG.RankThree.PartTwo.Sec4.Census.Res5L34

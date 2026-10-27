module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3WordsLinExc
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L35Group

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable [Fact (Nat.Prime 5)]

private noncomputable def heisU (a b c : GaloisField 5 1) : SL(3, GaloisField 5 1) :=
  ⟨!![1, a, c; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private theorem coe_heisU (a b c : GaloisField 5 1) :
    ((heisU a b c : SL(3, GaloisField 5 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) =
      !![1, a, c; 0, 1, b; 0, 0, 1] := rfl

private theorem heisU_congr {a b c a' b' c' : GaloisField 5 1} (ha : a = a') (hb : b = b')
    (hc : c = c') : heisU a b c = heisU a' b' c' := by
  rw [ha, hb, hc]

private theorem heisU_mul (a b c a' b' c' : GaloisField 5 1) :
    heisU a b c * heisU a' b' c' = heisU (a + a') (b + b') (c + c' + a * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_heisU, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem heisU_zero : heisU 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_heisU]

private theorem heisU_inv (a b c : GaloisField 5 1) :
    (heisU a b c)⁻¹ = heisU (-a) (-b) (a * b - c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [heisU_mul, ← heisU_zero]
  exact heisU_congr (by ring) (by ring) (by ring)

private theorem heisU_pow_five (a b c : GaloisField 5 1) : heisU a b c ^ 5 = 1 := by
  have h5 := five_eq_zero_galoisField_five_one
  have e : heisU a b c ^ 5 =
      heisU a b c * heisU a b c * heisU a b c * heisU a b c * heisU a b c := by
    simp only [pow_succ, pow_zero, one_mul]
  rw [e, heisU_mul, heisU_mul, heisU_mul, heisU_mul, ← heisU_zero]
  exact heisU_congr (by linear_combination a * h5) (by linear_combination b * h5)
    (by linear_combination (c + 2 * (a * b)) * h5)

private noncomputable def heisUT : Subgroup (projectiveSL 3 (GaloisField 5 1)) where
  carrier := {g | ∃ a b c, proj 3 _ (heisU a b c) = g}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, by rw [← map_mul, heisU_mul]⟩
  one_mem' := ⟨0, 0, 0, by rw [heisU_zero, map_one]⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, by rw [← map_inv, heisU_inv]⟩

private theorem heisU_commutator (a₁ b₁ c₁ a₂ b₂ c₂ : GaloisField 5 1) :
    heisU a₁ b₁ c₁ * heisU a₂ b₂ c₂ * (heisU a₁ b₁ c₁)⁻¹ * (heisU a₂ b₂ c₂)⁻¹ =
      heisU 0 0 (a₁ * b₂ - a₂ * b₁) := by
  rw [heisU_inv, heisU_inv, heisU_mul, heisU_mul, heisU_mul]
  exact heisU_congr (by ring) (by ring) (by ring)

private theorem heisU_center_comm (z a b c : GaloisField 5 1) :
    heisU 0 0 z * heisU a b c = heisU a b c * heisU 0 0 z := by
  rw [heisU_mul, heisU_mul]
  exact heisU_congr (by ring) (by ring) (by ring)

private theorem heis1412_heisU {a₁ b₁ c₁ a₂ b₂ c₂ : GaloisField 5 1}
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    Heis1412 (proj 3 _ (heisU a₁ b₁ c₁)) (proj 3 _ (heisU a₂ b₂ c₂)) := by
  have hcomm : proj 3 (GaloisField 5 1) (heisU a₁ b₁ c₁) * proj 3 _ (heisU a₂ b₂ c₂) *
      (proj 3 _ (heisU a₁ b₁ c₁))⁻¹ * (proj 3 _ (heisU a₂ b₂ c₂))⁻¹ =
      proj 3 _ (heisU 0 0 (a₁ * b₂ - a₂ * b₁)) := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, heisU_commutator]
  have hcz : ∀ a b c : GaloisField 5 1, Commute (proj 3 _ (heisU 0 0 (a₁ * b₂ - a₂ * b₁)))
      (proj 3 _ (heisU a b c)) := fun a b c => by
    change _ * _ = _ * _
    rw [← map_mul, ← map_mul, heisU_center_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hle : Subgroup.closure ({proj 3 _ (heisU a₁ b₁ c₁), proj 3 _ (heisU a₂ b₂ c₂)} :
        Set (projectiveSL 3 (GaloisField 5 1))) ≤ heisUT := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨a₁, b₁, c₁, rfl⟩
      · exact ⟨a₂, b₂, c₂, rfl⟩
    intro g
    obtain ⟨a, b, c, hg⟩ := hle g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hg, ← map_pow, heisU_pow_five, map_one, Subgroup.coe_one]
  · rw [← map_pow, heisU_pow_five, map_one]
  · rw [hcomm]
    intro h1
    have e := congrArg (fun g : SL(3, GaloisField 5 1) =>
      (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) 0 2)
      (proj_injective_five (h1.trans (map_one _).symm))
    simp [coe_heisU] at e
    exact hdet e
  · rw [hcomm]
    exact hcz _ _ _
  · rw [hcomm]
    exact hcz _ _ _

private noncomputable def heisT : SL(3, GaloisField 5 1) :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

private theorem coe_heisT :
    ((heisT : SL(3, GaloisField 5 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) =
      !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := rfl

private theorem heisT_mul_self : heisT * heisT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_heisT, Matrix.mul_apply, Fin.sum_univ_three]

private theorem heisT_conj (a b c : GaloisField 5 1) :
    heisT * heisU a b c * heisT⁻¹ = heisU (-a) (-b) c := by
  rw [inv_eq_of_mul_eq_one_right heisT_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_heisT, coe_heisU, Matrix.mul_apply, Fin.sum_univ_three]

private theorem excl1412_conj_L3_5 : Excl1412 (MulAut.conj (proj 3 (GaloisField 5 1) heisT)) := by
  have h5 := five_eq_zero_galoisField_five_one
  have key : ∀ a b : GaloisField 5 1,
      MulAut.conj (proj 3 (GaloisField 5 1) heisT) (proj 3 _ (heisU a b 0)) *
        (proj 3 _ (heisU a b 0))⁻¹ = proj 3 _ (heisU (-a + -a) (-b + -b) (a * b + a * b)) :=
      fun a b => by
    rw [MulAut.conj_apply, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, heisT_conj,
      heisU_inv, heisU_mul]
    exact congrArg _ (heisU_congr rfl rfl (by ring))
  refine Or.inr (Or.inr ⟨proj 3 _ (heisU 2 0 0), proj 3 _ (heisU 0 2 0), _, _,
    Subgroup.subset_closure (Set.mem_insert _ _),
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)), ?_⟩)
  rw [key, key]
  refine heis1412_heisU fun h => one_ne_zero (α := GaloisField 5 1) ?_
  linear_combination h - 3 * h5

private theorem dualAut_mul_inv_eq (X A : SL(3, GaloisField 5 1)) (h : X * X.transpose * A = 1) :
    dualAut 3 (GaloisField 5 1) (proj 3 _ X) * (proj 3 _ X)⁻¹ = proj 3 _ A := by
  rw [dualAut_proj, ← map_inv, ← map_mul, inv_transpose_eq_transpose_inv_exc,
    ← _root_.mul_inv_rev]
  exact congrArg _ (eq_inv_of_mul_eq_one_right h).symm

private noncomputable def l35gX₁ : SL(3, GaloisField 5 1) :=
  ⟨!![0, 1, 2; 0, 0, -2; 2, -1, -2], by
    have h5 := five_eq_zero_galoisField_five_one
    rw [Matrix.det_fin_three]
    simp
    linear_combination -h5⟩

private theorem coe_l35gX₁ :
    ((l35gX₁ : SL(3, GaloisField 5 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) =
      !![0, 1, 2; 0, 0, -2; 2, -1, -2] := rfl

private noncomputable def l35gX₂ : SL(3, GaloisField 5 1) :=
  ⟨!![0, 0, 2; 1, -2, 2; 2, -1, 0], by
    have h5 := five_eq_zero_galoisField_five_one
    rw [Matrix.det_fin_three]
    simp
    linear_combination h5⟩

private theorem coe_l35gX₂ :
    ((l35gX₂ : SL(3, GaloisField 5 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) =
      !![0, 0, 2; 1, -2, 2; 2, -1, 0] := rfl

private noncomputable def l35gA : SL(3, GaloisField 5 1) :=
  ⟨!![0, 1, -1; 1, 0, 0; -1, 0, -1], by simp [Matrix.det_fin_three]⟩

private theorem coe_l35gA :
    ((l35gA : SL(3, GaloisField 5 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) =
      !![0, 1, -1; 1, 0, 0; -1, 0, -1] := rfl

private noncomputable def l35gB : SL(3, GaloisField 5 1) :=
  ⟨!![-1, 0, 1; 0, 0, -1; 1, -1, 0], by simp [Matrix.det_fin_three]⟩

private theorem coe_l35gB :
    ((l35gB : SL(3, GaloisField 5 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) =
      !![-1, 0, 1; 0, 0, -1; 1, -1, 0] := rfl

private noncomputable def l35gG : SL(3, GaloisField 5 1) :=
  ⟨!![0, 0, 1; 1, 0, -1; 0, 1, 2], by simp [Matrix.det_fin_three]⟩

private theorem coe_l35gG :
    ((l35gG : SL(3, GaloisField 5 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) =
      !![0, 0, 1; 1, 0, -1; 0, 1, 2] := rfl

private theorem coe_l35gX₁_transpose :
    ((l35gX₁.transpose : SL(3, GaloisField 5 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) =
      !![0, 0, 2; 1, 0, -1; 2, -2, -2] := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_l35gX₁]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem coe_l35gX₂_transpose :
    ((l35gX₂.transpose : SL(3, GaloisField 5 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) =
      !![0, 1, 2; 0, -2, -1; 2, 2, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_l35gX₂]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem l35gX₁_mul : l35gX₁ * l35gX₁.transpose * l35gA = 1 := by
  have h5 := five_eq_zero_galoisField_five_one
  have hm : (!![0, 1, 2; 0, 0, -2; 2, -1, -2] : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) *
      !![0, 0, 2; 1, 0, -1; 2, -2, -2] * !![0, 1, -1; 1, 0, 0; -1, 0, -1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_l35gX₁_transpose,
    coe_l35gX₁, coe_l35gA, Matrix.SpecialLinearGroup.coe_one]
  exact hm

private theorem l35gX₂_mul : l35gX₂ * l35gX₂.transpose * l35gB = 1 := by
  have h5 := five_eq_zero_galoisField_five_one
  have hm : (!![0, 0, 2; 1, -2, 2; 2, -1, 0] : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) *
      !![0, 1, 2; 0, -2, -1; 2, 2, 0] * !![-1, 0, 1; 0, 0, -1; 1, -1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_l35gX₂_transpose,
    coe_l35gX₂, coe_l35gB, Matrix.SpecialLinearGroup.coe_one]
  exact hm

private theorem l35gG_conj_c : l35gG * (l35gA * l35gB * l35gB) = heisU (-1) 0 1 * l35gG := by
  have h5 := five_eq_zero_galoisField_five_one
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_l35gG, coe_l35gA, coe_l35gB, coe_heisU, Matrix.mul_apply, Fin.sum_univ_three] <;>
      grind

private theorem l35gG_conj_d : l35gG * (l35gB * l35gA * l35gB) = heisU 0 (-1) 1 * l35gG := by
  have h5 := five_eq_zero_galoisField_five_one
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_l35gG, coe_l35gA, coe_l35gB, coe_heisU, Matrix.mul_apply, Fin.sum_univ_three] <;>
      grind

private theorem excl1412_dualAut_L3_5 : Excl1412 (dualAut 3 (GaloisField 5 1)) := by
  have ha := dualAut_mul_inv_eq _ _ l35gX₁_mul
  have hb := dualAut_mul_inv_eq _ _ l35gX₂_mul
  set a := dualAut 3 (GaloisField 5 1) (proj 3 _ l35gX₁) * (proj 3 _ l35gX₁)⁻¹ with ha'
  set b := dualAut 3 (GaloisField 5 1) (proj 3 _ l35gX₂) * (proj 3 _ l35gX₂)⁻¹ with hb'
  have hamem : a ∈ Subgroup.closure ({a, b} : Set (projectiveSL 3 (GaloisField 5 1))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbmem : b ∈ Subgroup.closure ({a, b} : Set (projectiveSL 3 (GaloisField 5 1))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine Or.inr (Or.inr ⟨proj 3 _ l35gX₁, proj 3 _ l35gX₂, a * b * b, b * a * b,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hamem hbmem) hbmem,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hbmem hamem) hbmem, ?_⟩)
  refine Heis1412.map_equiv (MulAut.conj (proj 3 _ l35gG)) ?_
  have hc : MulAut.conj (proj 3 _ l35gG) (a * b * b) = proj 3 _ (heisU (-1) 0 1) := by
    rw [MulAut.conj_apply, ha, hb, ← map_mul, ← map_mul, ← map_mul, ← map_inv, ← map_mul,
      mul_inv_eq_iff_eq_mul.mpr l35gG_conj_c]
  have hd : MulAut.conj (proj 3 _ l35gG) (b * a * b) = proj 3 _ (heisU 0 (-1) 1) := by
    rw [MulAut.conj_apply, ha, hb, ← map_mul, ← map_mul, ← map_mul, ← map_inv, ← map_mul,
      mul_inv_eq_iff_eq_mul.mpr l35gG_conj_d]
  rw [hc, hd]
  refine heis1412_heisU fun h => one_ne_zero (α := GaloisField 5 1) ?_
  linear_combination h

theorem excl1412_L3_5 (β : MulAut (projectiveSL 3 (GaloisField 5 1))) (hβ : orderOf β = 2) :
    Excl1412 β := by
  have ht : orderOf (proj 3 (GaloisField 5 1) heisT) = 2 := by
    refine orderOf_eq_prime (by rw [sq, ← map_mul, heisT_mul_self, map_one]) fun h1 => ?_
    have e := congrArg (fun g : SL(3, GaloisField 5 1) =>
      (g : Matrix (Fin 3) (Fin 3) (GaloisField 5 1)) 0 0)
      (proj_injective_five (h1.trans (map_one _).symm))
    have h5 := five_eq_zero_galoisField_five_one
    simp [coe_heisT] at e
    exact one_ne_zero (α := GaloisField 5 1) (by linear_combination h5 + 2 * e)
  exact excl1412_projectiveSL3_of_exc (p := 5) (by norm_num) ht excl1412_conj_L3_5
    excl1412_dualAut_L3_5 β hβ

end CFSG.RankThree.PartTwo.Sec20

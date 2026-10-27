module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Irr

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def lineC (p : ℕ) [Fact p.Prime] : Subgroup (PSL3 p) :=
  (linePar p).map (piL p)

@[expose] noncomputable def planeC (p : ℕ) [Fact p.Prime] : Subgroup (PSL3 p) :=
  (planePar p).map (piL p)

theorem ker_piL_le_linePar : (piL p).ker ≤ linePar p :=
  ker_piL_le_leviBlock.trans leviBlock_le_linePar

theorem ker_piL_le_planePar : (piL p).ker ≤ planePar p :=
  ker_piL_le_leviBlock.trans leviBlock_le_planePar

theorem leviC_le_lineC : leviC p ≤ lineC p := Subgroup.map_mono leviBlock_le_linePar

theorem leviC_le_planeC : leviC p ≤ planeC p := Subgroup.map_mono leviBlock_le_planePar

theorem comap_lineC : (lineC p).comap (piL p) = linePar p :=
  Subgroup.comap_map_eq_self ker_piL_le_linePar

theorem comap_planeC : (planeC p).comap (piL p) = planePar p :=
  Subgroup.comap_map_eq_self ker_piL_le_planePar

theorem comap_leviC : (leviC p).comap (piL p) = leviBlock p :=
  Subgroup.comap_map_eq_self ker_piL_le_leviBlock

theorem odd_index_of_levi_le (hp2 : p ≠ 2) {Y : Subgroup SL(3, ZMod p)} (hB : leviBlock p ≤ Y) :
    Odd Y.index :=
  Odd.of_dvd_nat (odd_index_leviBlock hp2) (Subgroup.index_dvd_of_le hB)

theorem uMat_not_mem_planePar : uMat ![1, 0] ∉ planePar p := fun h => by
  have := h.1
  simp [coe_uMat] at this

@[expose] def upperRight (p : ℕ) [Fact p.Prime] : SL(3, ZMod p) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by norm_num [Matrix.det_fin_three]⟩

theorem upperRight_mem_planePar : upperRight p ∈ planePar p := by
  rw [mem_planePar_iff]
  simp [upperRight]

theorem upperRight_not_mem_linePar : upperRight p ∉ linePar p := fun h => by
  have := h.1
  simp [upperRight] at this

theorem linePar_sup_planePar (hirr : SL3OddIrr) (hp2 : p ≠ 2) :
    linePar p ⊔ planePar p = ⊤ := by
  have hB : leviBlock p ≤ linePar p ⊔ planePar p := leviBlock_le_linePar.trans le_sup_left
  refine eq_top_of_irreducible_of_levi hirr hp2 hB (odd_index_of_levi_le hp2 hB) ?_
  by_contra hred
  rcases le_linePar_or_le_planePar hB hred with h | h
  · exact upperRight_not_mem_linePar (h (Subgroup.mem_sup_right upperRight_mem_planePar))
  · exact uMat_not_mem_planePar (h (Subgroup.mem_sup_left (uMat_mem_linePar _)))

theorem lineC_sup_planeC (hirr : SL3OddIrr) (hp2 : p ≠ 2) :
    lineC p ⊔ planeC p = ⊤ := by
  rw [lineC, planeC, ← Subgroup.map_sup, linePar_sup_planePar hirr hp2]
  exact Subgroup.map_top_of_surjective _ piL_surjective

theorem lineC_ne_planeC : lineC p ≠ planeC p := fun h => by
  have := congrArg (Subgroup.comap (piL p)) h
  rw [comap_lineC, comap_planeC] at this
  exact uMat_not_mem_planePar (this ▸ uMat_mem_linePar _)

theorem lineC_ne_top : lineC p ≠ ⊤ := fun h => by
  have : linePar p = ⊤ := by rw [← comap_lineC, h, Subgroup.comap_top]
  exact upperRight_not_mem_linePar (this ▸ Subgroup.mem_top _)

theorem planeC_ne_top : planeC p ≠ ⊤ := fun h => by
  have : planePar p = ⊤ := by rw [← comap_planeC, h, Subgroup.comap_top]
  exact uMat_not_mem_planePar (this ▸ Subgroup.mem_top _)

theorem card_lineC_eq_planeC : Nat.card (lineC p) = Nat.card (planeC p) := by
  have h1 := Subgroup.card_mul_index (lineC p)
  have h2 := Subgroup.card_mul_index (planeC p)
  have hi1 : (lineC p).index = (linePar p).index :=
    Subgroup.index_map_eq _ piL_surjective ker_piL_le_linePar
  have hi2 : (planeC p).index = (planePar p).index :=
    Subgroup.index_map_eq _ piL_surjective ker_piL_le_planePar
  have hi : (planePar p).index = (linePar p).index := by
    rw [planePar_eq_map]
    exact Subgroup.index_map_equiv (linePar p) (slTau p)
  rw [hi2, hi, ← hi1] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (h1.trans h2.symm)

theorem map_comap_piL (Y : Subgroup (PSL3 p)) : (Y.comap (piL p)).map (piL p) = Y :=
  Subgroup.map_comap_eq_self_of_surjective piL_surjective Y

theorem leviBlock_le_comap {Y : Subgroup (PSL3 p)} (hB : leviC p ≤ Y) :
    leviBlock p ≤ Y.comap (piL p) := fun x hx => hB ⟨x, hx, rfl⟩

theorem le_parabolics_of_le_levi (hirr : SL3OddIrr) (hp2 : p ≠ 2)
    {Y : Subgroup (PSL3 p)} (hB : leviC p ≤ Y) (hY : Y ≠ ⊤) : Y ≤ lineC p ∨ Y ≤ planeC p := by
  have hBt := leviBlock_le_comap hB
  have hYt : Y.comap (piL p) ≠ ⊤ := fun h => hY (by
    rw [← map_comap_piL Y, h]
    exact Subgroup.map_top_of_surjective _ piL_surjective)
  have hred : ¬ IsIrreducibleSL3 (Y.comap (piL p)) := fun hirr' =>
    hYt (eq_top_of_irreducible_of_levi hirr hp2 hBt (odd_index_of_levi_le hp2 hBt) hirr')
  rcases le_linePar_or_le_planePar hBt hred with h | h
  · left
    rw [← map_comap_piL Y]
    exact Subgroup.map_mono h
  · right
    rw [← map_comap_piL Y]
    exact Subgroup.map_mono h

theorem eq_levi_or_eq_lineC {Y : Subgroup (PSL3 p)} (hB : leviC p ≤ Y) (hY : Y ≤ lineC p) :
    Y = leviC p ∨ Y = lineC p := by
  have h := eq_leviBlock_or_eq_linePar (leviBlock_le_comap hB)
    (comap_lineC (p := p) ▸ Subgroup.comap_mono hY)
  rcases h with h | h
  · left
    rw [← map_comap_piL Y, h]
    rfl
  · right
    rw [← map_comap_piL Y, h]
    rfl

theorem eq_levi_or_eq_planeC {Y : Subgroup (PSL3 p)} (hB : leviC p ≤ Y) (hY : Y ≤ planeC p) :
    Y = leviC p ∨ Y = planeC p := by
  have h := eq_leviBlock_or_eq_planePar (leviBlock_le_comap hB)
    (comap_planeC (p := p) ▸ Subgroup.comap_mono hY)
  rcases h with h | h
  · left
    rw [← map_comap_piL Y, h]
    rfl
  · right
    rw [← map_comap_piL Y, h]
    rfl

end CFSG.Quasithin.E2P.Asc80

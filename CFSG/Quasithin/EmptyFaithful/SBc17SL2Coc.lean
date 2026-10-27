module

public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Defs
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin

namespace SBc17

namespace Coc

variable {F : Type} [Field F]

theorem ext4 {g h : SL2 F} (h00 : g.1 0 0 = h.1 0 0) (h01 : g.1 0 1 = h.1 0 1)
    (h10 : g.1 1 0 = h.1 1 0) (h11 : g.1 1 1 = h.1 1 1) : g = h := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

theorem det_eq (g : SL2 F) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have := g.2
  rwa [Matrix.det_fin_two] at this

theorem mul00 (g h : SL2 F) :
    (g * h).1 0 0 = g.1 0 0 * h.1 0 0 + g.1 0 1 * h.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul01 (g h : SL2 F) :
    (g * h).1 0 1 = g.1 0 0 * h.1 0 1 + g.1 0 1 * h.1 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul10 (g h : SL2 F) :
    (g * h).1 1 0 = g.1 1 0 * h.1 0 0 + g.1 1 1 * h.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul11 (g h : SL2 F) :
    (g * h).1 1 1 = g.1 1 0 * h.1 0 1 + g.1 1 1 * h.1 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv00 (g : SL2 F) : (g⁻¹).1 0 0 = g.1 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv01 (g : SL2 F) : (g⁻¹).1 0 1 = -g.1 0 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv10 (g : SL2 F) : (g⁻¹).1 1 0 = -g.1 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv11 (g : SL2 F) : (g⁻¹).1 1 1 = g.1 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem uElt00 (x : F) : (uElt x : SL2 F).1 0 0 = 1 := by simp [uElt]
theorem uElt01 (x : F) : (uElt x : SL2 F).1 0 1 = x := by simp [uElt]
theorem uElt10 (x : F) : (uElt x : SL2 F).1 1 0 = 0 := by simp [uElt]
theorem uElt11 (x : F) : (uElt x : SL2 F).1 1 1 = 1 := by simp [uElt]

theorem tElt00 (a : Fˣ) : (tElt a : SL2 F).1 0 0 = a := by simp [tElt]
theorem tElt01 (a : Fˣ) : (tElt a : SL2 F).1 0 1 = 0 := by simp [tElt]
theorem tElt10 (a : Fˣ) : (tElt a : SL2 F).1 1 0 = 0 := by simp [tElt]
theorem tElt11 (a : Fˣ) : (tElt a : SL2 F).1 1 1 = (a : F)⁻¹ := by simp [tElt]

theorem wElt00 : (wElt : SL2 F).1 0 0 = 0 := by simp [wElt]
theorem wElt01 : (wElt : SL2 F).1 0 1 = 1 := by simp [wElt]
theorem wElt10 : (wElt : SL2 F).1 1 0 = -1 := by simp [wElt]
theorem wElt11 : (wElt : SL2 F).1 1 1 = 0 := by simp [wElt]

theorem uElt_injective : Function.Injective (uElt : F → SL2 F) := by
  intro x y h
  have := congrArg (fun g : SL2 F => g.1 0 1) h
  simpa [uElt01] using this

theorem tElt_mul_uElt (a : Fˣ) (x : F) : tElt a * uElt x = uElt ((a : F) ^ 2 * x) * tElt a := by
  refine ext4 ?_ ?_ ?_ ?_ <;>
    simp [mul00, mul01, mul10, mul11, uElt00, uElt01, uElt10, uElt11, tElt00, tElt01, tElt10,
      tElt11]
  field_simp

theorem tElt_mul (a b : Fˣ) : (tElt a : SL2 F) * tElt b = tElt (a * b) := by
  refine ext4 ?_ ?_ ?_ ?_ <;>
    simp [mul00, mul01, mul10, mul11, tElt00, tElt01, tElt10, tElt11]
  exact mul_comm _ _

theorem wElt_mul_tElt (a : Fˣ) : (wElt : SL2 F) * tElt a = tElt a⁻¹ * wElt := by
  refine ext4 ?_ ?_ ?_ ?_ <;>
    simp [mul00, mul01, mul10, mul11, wElt00, wElt01, wElt10, wElt11, tElt00, tElt01, tElt10,
      tElt11]

theorem uElt_mem_borelSub (x : F) : (uElt x : SL2 F) ∈ borelSub F := by
  rw [mem_borelSub_iff, uElt10]

theorem tElt_mem_borelSub (a : Fˣ) : (tElt a : SL2 F) ∈ borelSub F := by
  rw [mem_borelSub_iff, tElt10]

theorem exists_uElt_mul_tElt {b : SL2 F} (hb : b ∈ borelSub F) :
    ∃ (z : F) (a : Fˣ), b = uElt z * tElt a := by
  rw [mem_borelSub_iff] at hb
  have hdet := det_eq b
  rw [hb, mul_zero, sub_zero] at hdet
  have hne : b.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨b.1 0 1 * b.1 0 0, Units.mk0 _ hne, ?_⟩
  refine ext4 ?_ ?_ ?_ ?_ <;>
    simp [mul00, mul01, mul10, mul11, uElt00, uElt01, uElt10, uElt11, tElt00, tElt01, tElt10,
      tElt11, hb]
  · field_simp
  · exact eq_inv_of_mul_eq_one_right hdet

theorem bruhat {g : SL2 F} (hg : g ∉ borelSub F) :
    ∃ b₁ ∈ borelSub F, ∃ b₂ ∈ borelSub F, g = b₁ * wElt * b₂ := by
  rw [mem_borelSub_iff] at hg
  have hneg : -g.1 1 0 ≠ 0 := neg_ne_zero.mpr hg
  refine ⟨uElt (g.1 0 0 / g.1 1 0), uElt_mem_borelSub _,
    tElt (Units.mk0 _ hneg) * uElt (g.1 1 1 / g.1 1 0),
    (borelSub F).mul_mem (tElt_mem_borelSub _) (uElt_mem_borelSub _), ?_⟩
  have hdet := det_eq g
  refine ext4 ?_ ?_ ?_ ?_ <;>
    simp [mul00, mul01, mul10, mul11, uElt00, uElt01, uElt10, uElt11, tElt00, tElt01, tElt10,
      tElt11, wElt00, wElt01, wElt10, wElt11]
  all_goals field_simp
  linear_combination (-1 : F) * hdet

theorem exists_unit_ne_one [Fintype F] [DecidableEq F] (hq : 4 ≤ Fintype.card F) :
    ∃ a : Fˣ, a ≠ 1 := by
  have h : 1 < Fintype.card Fˣ := by
    rw [Fintype.card_units]
    omega
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h 1
  exact ⟨b, hb⟩

theorem braid [CharP F 2] : (uElt 1 : SL2 F) * wElt * uElt 1 * wElt = wElt * uElt 1 := by
  refine ext4 ?_ ?_ ?_ ?_ <;>
    simp [mul00, mul01, mul10, mul11, uElt00, uElt01, uElt10, uElt11, wElt00, wElt01, wElt10,
      wElt11, CharTwo.neg_eq]
  exact CharTwo.add_self_eq_zero 1

theorem cocycle_wElt (a : Fˣ) (ha : a ≠ 1) (d : SL2 F → (Fin 2 → F))
    (hd : ∀ g h : SL2 F, d (g * h) = d g + (g : Matrix (Fin 2) (Fin 2) F).mulVec (d h))
    (hB : ∀ b ∈ borelSub F, d b = 0) : d wElt = 0 := by
  have h1 := hd wElt (tElt a)
  have h2 := hd (tElt a⁻¹) wElt
  rw [hB _ (tElt_mem_borelSub a), Matrix.mulVec_zero, add_zero] at h1
  rw [hB _ (tElt_mem_borelSub a⁻¹), zero_add] at h2
  rw [wElt_mul_tElt, h2] at h1
  have hne : (a : F) - 1 ≠ 0 := sub_ne_zero.mpr fun h => ha (Units.ext h)
  have hne' : (a : F)⁻¹ - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h => ha (Units.ext (inv_eq_one.mp h))
  have h0 : d wElt 0 = 0 := by
    have := congrFun h1 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, tElt00, tElt01] at this
    have h3 : ((a : F)⁻¹ - 1) * d wElt 0 = 0 := by linear_combination this
    exact (mul_eq_zero.mp h3).resolve_left hne'
  have h1' : d wElt 1 = 0 := by
    have := congrFun h1 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, tElt10, tElt11] at this
    have h3 : ((a : F) - 1) * d wElt 1 = 0 := by linear_combination this
    exact (mul_eq_zero.mp h3).resolve_left hne
  funext i
  fin_cases i
  · exact h0
  · exact h1'

theorem unit_sq_ne_one [CharP F 2] (a : Fˣ) (ha : a ≠ 1) : (a : F) ^ 2 ≠ 1 := by
  intro h
  apply ha
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : ((a : F) - 1) ^ 2 = 0 := by linear_combination h + (1 - (a : F)) * h2
  exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))

theorem eq_id_of_fixes_borel [Fintype F] [DecidableEq F] [CharP F 2] (hq : 4 ≤ Fintype.card F)
    (ψ : SL2 F →* SL2 F) (hψ : ∀ b ∈ borelSub F, ψ b = b) : ∀ g : SL2 F, ψ g = g := by
  obtain ⟨a, ha⟩ := exists_unit_ne_one hq
  have ha2 := unit_sq_ne_one a ha
  have hw : ψ wElt = wElt := by
    have hA : ψ wElt * tElt a = tElt a⁻¹ * ψ wElt := by
      have := congrArg ψ (wElt_mul_tElt a)
      simpa only [map_mul, hψ _ (tElt_mem_borelSub a), hψ _ (tElt_mem_borelSub a⁻¹)] using this
    have hB : uElt 1 * ψ wElt * uElt 1 * ψ wElt = ψ wElt * uElt 1 := by
      have := congrArg ψ (braid (F := F))
      simpa only [map_mul, hψ _ (uElt_mem_borelSub 1)] using this
    generalize ψ wElt = w' at hA hB ⊢
    have hdet := det_eq w'
    have h00 := congrArg (fun g : SL2 F => g.1 0 0) hA
    have h11 := congrArg (fun g : SL2 F => g.1 1 1) hA
    simp [mul00, mul11, tElt00, tElt01, tElt10, tElt11] at h00 h11
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    have hp : w'.1 0 0 = 0 := by
      have h3 : w'.1 0 0 * ((a : F) ^ 2 - 1) = 0 := by
        linear_combination (a : F) * h00 + w'.1 0 0 * mul_inv_cancel₀ ha0
      exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr ha2)
    have hs : w'.1 1 1 = 0 := by
      have h3 : w'.1 1 1 * (1 - (a : F) ^ 2) = 0 := by
        linear_combination (a : F) * h11 - w'.1 1 1 * mul_inv_cancel₀ ha0
      exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr (Ne.symm ha2))
    have b01 := congrArg (fun g : SL2 F => g.1 0 1) hB
    have b11 := congrArg (fun g : SL2 F => g.1 1 1) hB
    simp [mul00, mul01, mul10, mul11, uElt00, uElt01, uElt10, uElt11, hp, hs] at b01 b11
    have hqr : w'.1 0 1 = w'.1 1 0 := b01.symm.trans b11
    rw [hp, hs] at hdet
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h3 : (w'.1 0 1 - 1) ^ 2 = 0 := by
      linear_combination (-1 : F) * hdet + w'.1 0 1 * hqr - w'.1 0 1 * h2
    have hq1 : w'.1 0 1 = 1 :=
      sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
    refine ext4 ?_ ?_ ?_ ?_
    · rw [hp, wElt00]
    · rw [hq1, wElt01]
    · rw [wElt10, CharTwo.neg_eq, ← hqr, hq1]
    · rw [hs, wElt11]
  intro g
  by_cases hg : g ∈ borelSub F
  · exact hψ g hg
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := bruhat hg
    rw [map_mul, map_mul, hψ _ hb₁, hψ _ hb₂, hw]

theorem conj_uElt (z x : F) (a : Fˣ) :
    (uElt z * tElt a) * uElt x * (uElt z * tElt a)⁻¹ = uElt ((a : F) ^ 2 * x) := by
  refine ext4 ?_ ?_ ?_ ?_ <;>
    simp [mul00, mul01, mul10, mul11, inv00, inv01, inv10, inv11, uElt00, uElt01, uElt10, uElt11,
      tElt00, tElt01, tElt10, tElt11]
  field_simp
  ring

theorem conj_tElt (y : F) (s a : Fˣ) :
    (uElt y * tElt s) * tElt a * (uElt y * tElt s)⁻¹ = uElt (y * (1 - (a : F) ^ 2)) * tElt a := by
  refine ext4 ?_ ?_ ?_ ?_ <;>
    simp [mul00, mul01, mul10, mul11, inv00, inv01, inv10, inv11, uElt00, uElt01, uElt10, uElt11,
      tElt00, tElt01, tElt10, tElt11]
  all_goals field_simp
  ring

theorem conj_mul_conj (g u t : SL2 F) : g * u * g⁻¹ * (g * t * g⁻¹) = g * (u * t) * g⁻¹ := by
  simp only [mul_assoc, inv_mul_cancel_left]

theorem exists_conj_borel [Fintype F] [DecidableEq F] [CharP F 2]
    (hq : 4 ≤ Fintype.card F) (φ : MulAut (SL2 F))
    (hφ : ∀ b ∈ borelSub F, φ b * b⁻¹ ∈ upperSub F) :
    ∃ g : SL2 F, ∀ b ∈ borelSub F, φ b = g * b * g⁻¹ := by
  have hU : ∀ x : F, ∃ y : F, φ (uElt x) = uElt y := by
    intro x
    have h1 := hφ (uElt x) (uElt_mem_borelSub x)
    have h2 : uElt x ∈ upperSub F := mem_upperSub_iff.mpr ⟨x, rfl⟩
    have h3 := (upperSub F).mul_mem h1 h2
    rw [inv_mul_cancel_right] at h3
    exact mem_upperSub_iff.mp h3
  choose α hα using hU
  have hT : ∀ a : Fˣ, ∃ z : F, φ (tElt a) = uElt z * tElt a := by
    intro a
    obtain ⟨z, hz⟩ := mem_upperSub_iff.mp (hφ (tElt a) (tElt_mem_borelSub a))
    exact ⟨z, mul_inv_eq_iff_eq_mul.mp hz⟩
  choose z hz using hT
  have hadd : ∀ x y, α (x + y) = α x + α y := by
    intro x y
    apply uElt_injective
    have h := hα (x + y)
    rw [← uElt_mul, map_mul, hα, hα, uElt_mul] at h
    exact h.symm
  have hconj : ∀ (a : Fˣ) (x : F), α ((a : F) ^ 2 * x) = (a : F) ^ 2 * α x := by
    intro a x
    apply uElt_injective
    have hc : tElt a * uElt x * (tElt a)⁻¹ = uElt ((a : F) ^ 2 * x) :=
      mul_inv_eq_iff_eq_mul.mpr (tElt_mul_uElt a x)
    have h := congrArg φ hc
    rw [map_mul, map_mul, map_inv, hz a, hα, hα, conj_uElt] at h
    exact h.symm
  have hsq : ∀ s : F, ∃ r : F, s = r * r := fun s => isSquare_of_charTwo' s
  have hα0 : α 0 = 0 := by simpa using hadd 0 0
  have hlin : ∀ s : F, α s = α 1 * s := by
    intro s
    by_cases hs : s = 0
    · rw [hs, hα0, mul_zero]
    · obtain ⟨r, hr⟩ := hsq s
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact hs (by rw [hr, mul_zero])
      have h := hconj (Units.mk0 r hr0) 1
      simp only [Units.val_mk0, mul_one] at h
      rw [hr, ← pow_two, h, mul_comm]
  have hc0 : α 1 ≠ 0 := by
    intro h
    have h1 : φ (uElt 1) = 1 := by rw [hα, h, uElt_zero]
    have h2 : uElt (1 : F) = 1 := φ.injective (by rw [h1, map_one])
    have h3 := congrArg (fun g : SL2 F => g.1 0 1) h2
    simp [uElt01] at h3
  obtain ⟨σ, hσ⟩ := hsq (α 1)
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [hσ, mul_zero])
  obtain ⟨a₀, ha₀⟩ := exists_unit_ne_one hq
  have ha₀2 := unit_sq_ne_one a₀ ha₀
  have hd0 : (1 : F) - (a₀ : F) ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha₀2)
  have hz_rel : ∀ a : Fˣ, z a * (1 - (a₀ : F) ^ 2) = z a₀ * (1 - (a : F) ^ 2) := by
    intro a
    have h1 : (tElt a : SL2 F) * tElt a₀ = tElt a₀ * tElt a := by
      rw [tElt_mul, tElt_mul, mul_comm]
    have h2 := congrArg φ h1
    rw [map_mul, map_mul, hz a, hz a₀] at h2
    have h3 := congrArg (fun g : SL2 F => g.1 0 1) h2
    simp [mul01, mul00, mul11, uElt00, uElt01, uElt10, uElt11, tElt00, tElt01, tElt10,
      tElt11] at h3
    field_simp at h3
    linear_combination h3
  have hgU : ∀ x : F, φ (uElt x) =
      (uElt (z a₀ / (1 - (a₀ : F) ^ 2)) * tElt (Units.mk0 σ hσ0)) * uElt x *
        (uElt (z a₀ / (1 - (a₀ : F) ^ 2)) * tElt (Units.mk0 σ hσ0))⁻¹ := by
    intro x
    rw [conj_uElt, hα, hlin]
    congr 1
    show α 1 * x = σ ^ 2 * x
    rw [hσ]
    ring
  have hgT : ∀ a : Fˣ, φ (tElt a) =
      (uElt (z a₀ / (1 - (a₀ : F) ^ 2)) * tElt (Units.mk0 σ hσ0)) * tElt a *
        (uElt (z a₀ / (1 - (a₀ : F) ^ 2)) * tElt (Units.mk0 σ hσ0))⁻¹ := by
    intro a
    rw [conj_tElt, hz a]
    congr 2
    field_simp
    linear_combination hz_rel a
  refine ⟨uElt (z a₀ / (1 - (a₀ : F) ^ 2)) * tElt (Units.mk0 σ hσ0), ?_⟩
  intro b hb
  obtain ⟨z', a, rfl⟩ := exists_uElt_mul_tElt hb
  rw [map_mul, hgU, hgT, conj_mul_conj]

theorem eq_conj_of_borel [Fintype F] [DecidableEq F] [CharP F 2]
    (hq : 4 ≤ Fintype.card F) (φ : MulAut (SL2 F)) (g : SL2 F)
    (hg : ∀ b ∈ borelSub F, φ b = g * b * g⁻¹) : ∀ x : SL2 F, φ x = g * x * g⁻¹ := by
  have key := eq_id_of_fixes_borel hq ((MulAut.conj g⁻¹).toMonoidHom.comp φ.toMonoidHom) (by
    intro b hb
    simp [hg b hb, mul_assoc])
  intro x
  have h := key x
  simp at h
  calc φ x = g * (g⁻¹ * φ x * g) * g⁻¹ := by simp [mul_assoc]
    _ = g * x * g⁻¹ := by rw [h]

end Coc

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [CharP F 2] in
theorem cocycle_eq_zero (hq : 4 ≤ Fintype.card F) (d : SL2 F → (Fin 2 → F))
    (hd : ∀ g h : SL2 F, d (g * h) = d g + (g : Matrix (Fin 2) (Fin 2) F).mulVec (d h))
    (hB : ∀ b ∈ borelSub F, d b = 0) : ∀ g : SL2 F, d g = 0 := by
  obtain ⟨a, ha⟩ := Coc.exists_unit_ne_one hq
  have hw := Coc.cocycle_wElt a ha d hd hB
  intro g
  by_cases hg : g ∈ borelSub F
  · exact hB g hg
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Coc.bruhat hg
    rw [mul_assoc, hd, hB b₁ hb₁, zero_add, hd, hw, hB b₂ hb₂, Matrix.mulVec_zero, add_zero,
      Matrix.mulVec_zero]

theorem inner_of_trivial_mod_upper (hq : 4 ≤ Fintype.card F) (φ : MulAut (SL2 F))
    (hφ : ∀ b ∈ borelSub F, φ b * b⁻¹ ∈ upperSub F) :
    ∃ g : SL2 F, ∀ x : SL2 F, φ x = g * x * g⁻¹ := by
  obtain ⟨g, hg⟩ := Coc.exists_conj_borel hq φ hφ
  exact ⟨g, Coc.eq_conj_of_borel hq φ g hg⟩

end SBc17

end CFSG.Quasithin

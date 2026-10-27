module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.At

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem cj_cj_inv (g : Perm (Fin 5)) (A : Subgroup (Perm (Fin 5))) : cj g (cj g⁻¹ A) = A := by
  ext σ
  rw [mem_cj, mem_cj]
  have : (g⁻¹)⁻¹ * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
  rw [this]

theorem cj_le_cj_iff (g : Perm (Fin 5)) {A B : Subgroup (Perm (Fin 5))} :
    cj g A ≤ cj g B ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective (MulEquiv.injective _)

theorem isQuad_cj_iff (g : Perm (Fin 5)) (A : Subgroup (Perm (Fin 5))) :
    IsQuad (cj g A) ↔ IsQuad A := by
  unfold IsQuad
  rw [commW_cj_top]
  constructor
  · intro h x hx w hw
    have h1 := h (g * x * g⁻¹) (mem_cj_conj.mpr hx) (orth.act g w) ((mem_mp).mpr
      (by rw [act_inv_act]; exact hw))
    have h2 : orth.act (g * x * g⁻¹) (orth.act g w) = orth.act g (orth.act x w) := by
      rw [act_mul_apply, act_mul_apply, act_inv_act]
    rw [h2] at h1
    exact (orth.act g).injective h1
  · intro h a ha w hw
    rw [mem_mp] at hw
    have h1 := h (g⁻¹ * a * g) (mem_cj.mp ha) _ hw
    have h2 : orth.act (g⁻¹ * a * g) (orth.act g⁻¹ w) = orth.act g⁻¹ (orth.act a w) := by
      rw [act_mul_apply, act_mul_apply, act_act_inv]
    rw [h2] at h1
    exact (orth.act g⁻¹).injective h1

theorem quad_std_cases : ∀ a ∈ S5SylF, a ∉ S5ThatF → (∀ w ∈ commF a, orth.act a w = w) →
    a ^ 2 = 1 ∧ ∀ b ∈ S5SylF, (∀ w ∈ commF a, orth.act b w = w) → b = 1 ∨ b = a := by
  unfold commF; decide +kernel

theorem le_That_std_of_quad {B : Subgroup (Perm (Fin 5))} (hB : B ≤ S5Syl) (hq : IsQuad B) :
    B ≤ S5That ∨ Nat.card B ≤ 2 := by
  by_cases h : B ≤ S5That
  · exact Or.inl h
  right
  obtain ⟨a, ha, han⟩ := Set.not_subset.mp h
  have hq1 : ∀ b ∈ B, ∀ w ∈ commF a, orth.act b w = w := fun b hb w hw =>
    hq b hb w (commW_mono_left' (Subgroup.zpowers_le.mpr ha) _
      ((mem_commW_zpowers_iff a w).mpr hw))
  obtain ⟨h2, h3⟩ := quad_std_cases a ((mem_S5Syl_iff a).mp (hB ha))
    (fun h => han ((mem_S5That_iff a).mpr h)) (hq1 a ha)
  have hle : B ≤ Subgroup.zpowers a := by
    intro b hb
    rcases h3 b ((mem_S5Syl_iff b).mp (hB hb)) (hq1 b hb) with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  have hord : Nat.card (Subgroup.zpowers a) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
  exact (Subgroup.card_le_of_le hle).trans hord

theorem le_That_of_quad {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {A : Subgroup (Perm (Fin 5))} (hA : A ≤ D) (hq : IsQuad A) :
    A ≤ That D ∨ Nat.card A ≤ 2 := by
  obtain ⟨g, rfl, hT, -, -⟩ := std_data hD
  obtain ⟨B, rfl⟩ : ∃ B, A = cj g B := ⟨cj g⁻¹ A, (cj_cj_inv g A).symm⟩
  rw [cj_le_cj_iff] at hA
  rw [isQuad_cj_iff] at hq
  rw [hT, cj_le_cj_iff, card_cj]
  exact le_That_std_of_quad hA hq

theorem eq_That_of_quad {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {A : Subgroup (Perm (Fin 5))} (hA : A ≤ D) (hq : IsQuad A) (h4 : 4 ≤ Nat.card A) :
    A = That D := by
  rcases le_That_of_quad hD hA hq with h | h
  · exact Subgroup.eq_of_le_of_card_ge h (by rw [card_That hD]; exact h4)
  · omega

end CFSG.Quasithin.F53.Stellmacher.S35.At

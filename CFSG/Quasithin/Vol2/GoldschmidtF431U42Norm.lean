module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Ag2

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431
open scoped Pointwise

theorem le_T_of_le_B0
    {R : Subgroup Y} (hRB : R ≤ B0) (hp : IsPGroup 2 R) : R ≤ T := by
  have hT : IsPGroup 2 T := isSylow_T.2.1
  have hR : R ≤ Subgroup.normalizer (T : Set Y) := by
    rw [normalizer_T]
    exact hRB
  have hsup : IsPGroup 2 ↥(T ⊔ R) := hT.to_sup_of_normal_left' hp hR
  exact (eq_T_of_isPGroup le_sup_left hsup) ▸ le_sup_right

theorem normalizer_B0 :
    Subgroup.normalizer (B0 : Set Y) = B0 := by
  refine le_antisymm (fun y hy => ?_) (fun b hb => Subgroup.le_normalizer hb)
  have hmap : T.map (MulAut.conj y).toMonoidHom ≤ T := by
    refine le_T_of_le_B0 ?_ (isSylow_T.2.1.map _)
    rintro _ ⟨t, ht, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hy t).1 (T_le_B0 ht)
  have hcard : Nat.card T ≤ Nat.card (T.map (MulAut.conj y).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj y).injective).symm.le
  have heq := Subgroup.eq_of_le_of_card_ge hmap hcard
  rw [← normalizer_T]
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => hmap ⟨t, ht, rfl⟩, fun ht => ?_⟩
  rw [← heq] at ht
  obtain ⟨s, hs, hst⟩ := ht
  have : s = t := by
    have h2 : y * s * y⁻¹ = y * t * y⁻¹ := hst
    exact mul_left_cancel (mul_right_cancel h2)
  exact this ▸ hs

theorem yxyi_not_mem_P1 : (yY * xY * yY⁻¹) ∉ P1 := by
  rw [mem_P1_iff]
  intro h
  have hr : RepL (comp (comp yL xL) yiL) (((yY * xY * yY⁻¹ : Y)) : P45) :=
    repL_mul (repL_mul repL_y repL_x) repL_yi
  have h1 : (comp (comp yL xL) yiL).getD 0 0 = ((((yY * xY * yY⁻¹ : Y)) : P45) 0 : ℕ) := hr.2 0
  rw [h] at h1
  have h42 : (comp (comp yL xL) yiL).getD 0 0 = 42 := by decide +kernel
  rw [h42] at h1
  exact absurd h1 (by simp)

theorem yixy_not_mem_P2 : (yY⁻¹ * xY * yY) ∉ P2 := by
  rw [mem_P2_iff]
  intro h
  have hr : RepL (comp (comp yiL xL) yL) (((yY⁻¹ * xY * yY : Y)) : P45) :=
    repL_mul (repL_mul repL_yi repL_x) repL_y
  have h0 : (0 : Fin 45) ∈ L0S := zero_mem_L0S
  have h1 : (((yY⁻¹ * xY * yY : Y)) : P45) 0 ∈ L0S := by
    rw [← h]
    exact ⟨0, h0, rfl⟩
  have h2 : (comp (comp yiL xL) yL).getD 0 0 = ((((yY⁻¹ * xY * yY : Y)) : P45) 0 : ℕ) := hr.2 0
  have h2' : (comp (comp yiL xL) yL).getD 0 0 = 2 := by decide +kernel
  rw [h2'] at h2
  have h3 : ((((yY⁻¹ * xY * yY : Y)) : P45) 0 : ℕ) = 2 := h2.symm
  rw [L0S_eq] at h1
  have h4 : ((((yY⁻¹ * xY * yY : Y)) : P45) 0) = (2 : Fin 45) := Fin.ext h3
  rw [h4] at h1
  revert h1
  decide

theorem normalizer_P1 :
    Subgroup.normalizer (P1 : Set Y) = P1 := by
  have hP1 : P1 ≤ Subgroup.normalizer (P1 : Set Y) := Subgroup.le_normalizer
  rcases lattice (B0_le_P1.trans hP1) with h | h | h | h
  · exfalso
    have := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (h ▸ hP1 : P1 ≤ B0))
    rw [card_P1, card_B0] at this
    omega
  · exact h
  · exfalso
    have hle : P1 ≤ P2 := h ▸ hP1
    have htop : P2 = ⊤ := by rw [← P1_sup_P2, sup_eq_right.2 hle]
    have h1 := card_P2
    rw [htop, Subgroup.card_top, card_Xs] at h1
    omega
  · exfalso
    have hy : yY ∈ Subgroup.normalizer (P1 : Set Y) := h ▸ Subgroup.mem_top _
    have hx : xY ∈ P1 := B0_le_P1 (T_le_B0 xY_mem_T)
    exact yxyi_not_mem_P1 ((Subgroup.mem_normalizer_iff.1 hy xY).1 hx)

theorem normalizer_P2 :
    Subgroup.normalizer (P2 : Set Y) = P2 := by
  have hP2 : P2 ≤ Subgroup.normalizer (P2 : Set Y) := Subgroup.le_normalizer
  rcases lattice (B0_le_P2.trans hP2) with h | h | h | h
  · exfalso
    have := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (h ▸ hP2 : P2 ≤ B0))
    rw [card_P2, card_B0] at this
    omega
  · exfalso
    have hle : P2 ≤ P1 := h ▸ hP2
    have htop : P1 = ⊤ := by rw [← P1_sup_P2, sup_eq_left.2 hle]
    have h1 := card_P1
    rw [htop, Subgroup.card_top, card_Xs] at h1
    omega
  · exact h
  · exfalso
    have hy : yY⁻¹ ∈ Subgroup.normalizer (P2 : Set Y) := h ▸ Subgroup.mem_top _
    have hx : xY ∈ P2 := B0_le_P2 (T_le_B0 xY_mem_T)
    exact yixy_not_mem_P2 ((Subgroup.mem_normalizer_iff.1 hy xY).1 hx)

end CFSG.Quasithin.H13.F431.U42

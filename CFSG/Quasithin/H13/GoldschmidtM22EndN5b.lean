module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN5a
public import CFSG.Quasithin.H13.GoldschmidtM22EndN4d

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem pow_eq_seven_of_mul_eq {a m : ℕ} (hm : ¬ 2 ∣ m) (h : 2 ^ a * m = 1920) : a = 7 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h
  have h1 : a ≤ 10 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 11 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hlt
    nlinarith
  interval_cases a <;> omega

theorem centralizer_eq_of_le (h : Hyp6Sec2 G T M L V) (hA : Subgroup.centralizer (V : Set G) ≤ V) :
    Subgroup.centralizer (V : Set G) = V :=
  le_antisymm hA (V_le_centralizer_V h)

theorem card_T_of_caseA (h : Hyp6Sec2 G T M L V) (hA : Subgroup.centralizer (V : Set G) ≤ V)
    (hNeq : Subgroup.normalizer (V : Set G) = L ⊔ T)
    (e : ↥(autOn (L ⊔ T) V) ≃* Equiv.Perm (Fin 5)) : Nat.card ↥T = 128 := by
  have hN := card_normalizer hNeq e
  rw [centralizer_eq_of_le h hA, KData.card_V h] at hN
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer
  have h1 := Subgroup.relIndex_mul_card (H := T) (K := Subgroup.normalizer (V : Set G))
  rw [inf_eq_left.mpr hTN, hN] at h1
  have hodd : ¬ 2 ∣ T.relIndex (Subgroup.normalizer (V : Set G)) := fun hd =>
    h.sylow.2 (dvd_trans hd (Subgroup.relIndex_dvd_index_of_le hTN))
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp h.sylow.1
  rw [ha] at h1
  have := pow_eq_seven_of_mul_eq hodd (by rw [mul_comm]; omega)
  rw [ha, this]
  norm_num

end CFSG.Quasithin.H13.GM22

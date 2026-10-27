module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Basic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem eq_sup_zpowers_of_card {Z Θ : Subgroup D} (hZ : Z ≤ Θ) (hZc : Nat.card Z = 2)
    (hΘ : Nat.card Θ = 4) {c : D} (hc : c ∈ Θ) (hcZ : c ∉ Z) :
    Θ = Z ⊔ Subgroup.zpowers c := by
  have hS : Z ⊔ Subgroup.zpowers c ≤ Θ := sup_le hZ (Subgroup.zpowers_le.mpr hc)
  have d1 : 2 ∣ Nat.card ↥(Z ⊔ Subgroup.zpowers c) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Z ≤ Z ⊔ Subgroup.zpowers c)
    rwa [hZc] at this
  have d2 : Nat.card ↥(Z ⊔ Subgroup.zpowers c) ∣ 4 := by
    have := Subgroup.card_dvd_of_le hS
    rwa [hΘ] at this
  have hne : Nat.card ↥(Z ⊔ Subgroup.zpowers c) ≠ 2 := fun e => by
    have heq : Z = Z ⊔ Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [e, hZc])
    exact hcZ (heq ▸ (le_sup_right : Subgroup.zpowers c ≤ Z ⊔ Subgroup.zpowers c)
      (Subgroup.mem_zpowers c))
  have h4 : Nat.card ↥(Z ⊔ Subgroup.zpowers c) = 4 := by
    obtain ⟨k, hk⟩ := d1
    have := Nat.le_of_dvd (by norm_num) d2
    have hpos : 0 < Nat.card ↥(Z ⊔ Subgroup.zpowers c) := Nat.card_pos
    omega
  exact (Subgroup.eq_of_le_of_card_ge hS (by rw [h4, hΘ])).symm

end GoldAmL3

end F6

end CFSG.Quasithin

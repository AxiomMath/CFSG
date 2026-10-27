module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Basic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem comm_mul_eq (r m m' : D) :
    r * (m * m') * r⁻¹ * (m * m')⁻¹ =
      (r * m * r⁻¹ * m⁻¹) * (m * (r * m' * r⁻¹ * m'⁻¹) * m⁻¹) := by
  group

@[expose] def commIn (W K : Subgroup D) (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hK : K ≤ W)
    (r : D) : Subgroup D where
  carrier := {m | m ∈ W ∧ r * m * r⁻¹ * m⁻¹ ∈ K}
  mul_mem' := by
    rintro m m' ⟨hm, hmk⟩ ⟨hm', hm'k⟩
    refine ⟨W.mul_mem hm hm', ?_⟩
    have hb : m * (r * m' * r⁻¹ * m'⁻¹) * m⁻¹ = r * m' * r⁻¹ * m'⁻¹ := by
      rw [hW m hm _ (hK hm'k)]
      group
    rw [comm_mul_eq, hb]
    exact K.mul_mem hmk hm'k
  one_mem' := ⟨W.one_mem, by simp⟩
  inv_mem' := by
    rintro m ⟨hm, hmk⟩
    refine ⟨W.inv_mem hm, ?_⟩
    have hb : m⁻¹ * (r * m * r⁻¹ * m⁻¹)⁻¹ * m = (r * m * r⁻¹ * m⁻¹)⁻¹ := by
      rw [hW m⁻¹ (W.inv_mem hm) _ (hK (K.inv_mem hmk))]
      group
    have e : r * m⁻¹ * r⁻¹ * (m⁻¹)⁻¹ = m⁻¹ * (r * m * r⁻¹ * m⁻¹)⁻¹ * m := by group
    rw [e, hb]
    exact K.inv_mem hmk

end GoldAmL3

end F6

end CFSG.Quasithin

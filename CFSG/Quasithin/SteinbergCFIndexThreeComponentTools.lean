module

public import CFSG.Foundations.Basic
public import CFSG.Walter.AStar.Subnormal
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.SteinbergCF

open CFSG Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem isPGroup_center_of_isComponent (hO : pPrimeCore 2 H = ⊥) {K : Subgroup H}
    (hK : IsComponent K) : IsPGroup 2 (center K) := by
  intro z
  obtain ⟨k, m, hm, hz⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨k, ?_⟩
  have hodd : Odd (orderOf (z ^ 2 ^ k)) := by
    rw [orderOf_pow_of_dvd (by positivity) ⟨m, hz⟩, hz]
    simpa using hm
  set y : center K := z ^ 2 ^ k
  have hYn : (zpowers (y : K)).Normal :=
    normal_of_le_center (zpowers_le.mpr y.2)
  have hYs : ((zpowers (y : K)).map K.subtype).IsSubnormal :=
    IsSubnormal.trans' hYn.isSubnormal hK.2
  have hYo : Odd (Nat.card ((zpowers (y : K)).map K.subtype)) := by
    rw [card_map_of_injective K.subtype_injective, Nat.card_zpowers, orderOf_coe]
    exact hodd
  have hbot := CFSG.Walter.eq_bot_of_isSubnormal_of_odd hO hYs hYo
  rw [map_eq_bot_iff_of_injective _ K.subtype_injective, zpowers_eq_bot] at hbot
  exact Subtype.ext hbot

end CFSG.Quasithin.SteinbergCF

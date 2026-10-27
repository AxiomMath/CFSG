module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem mul_self_mem_of_relIndex_two {Q T : Subgroup D} (hidx : Q.relIndex T = 2) {t : D}
    (ht : t ∈ T) : t * t ∈ Q := by
  have := Subgroup.mul_self_mem_of_index_two hidx ⟨t, ht⟩
  rwa [Subgroup.mem_subgroupOf] at this

variable [Finite D]

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_mem_inf_not_mem_pCoreOf_right : ∃ t ∈ A ⊓ B, t ∉ pCoreOf 2 B := by
  by_contra hcon
  push Not at hcon
  have := Subgroup.relIndex_eq_one.mpr (fun t ht => hcon t ht)
  rw [h.gold.relIndex_pCoreOf_T_right] at this
  omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin

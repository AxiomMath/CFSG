module

public import CFSG.Quasithin.Recognition.HSTypeZQ

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem mul_self_of_mem_V (h : HSSetting z V) {v : G} (hv : v ∈ V) : v * v = 1 := by
  have := h.elem.2 v hv
  rwa [sq] at this

theorem comm_of_mem_V (h : HSSetting z V) {v w : G} (hv : v ∈ V) (hw : w ∈ V) :
    v * w = w * v :=
  congrArg Subtype.val (h.elem.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)

theorem eq_one_or_z_of_mem_V_ZQ [Finite G] (h : HSSetting z V) {v : G} (hv : v ∈ V)
    (hvZ : v ∈ hsZQ z) : v = 1 ∨ v = z := by
  by_cases h1 : v = 1
  · exact Or.inl h1
  · exact Or.inr (h.eq_z_of_mem_ZQ hvZ (h.mul_self_of_mem_V hv) h1)

end HSSetting

end CFSG.Quasithin.HSType

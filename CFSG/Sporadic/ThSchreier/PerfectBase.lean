
module

public import CFSG.Certificates.ExtraspecialNormalForm
public import CFSG.Sporadic.Th.Max3.QuotientBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates
open scoped commutatorElement

theorem isPerfect_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hm : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [commutator_def, hb, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · rw [commutator_def]
    exact ht

theorem aPerm_mul_bPerm_ne : aPerm * bPerm ≠ bPerm * aPerm := by decide

end CFSG.Sporadic.ThSchreier

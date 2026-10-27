module

public import CFSG.Monster.GMS.ASegConn
public import CFSG.Monster.GMS.ASegConnCo1

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem twoAGraph_reachable_of_mem_leechQ
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {z x y : G} (hz : IsConj z₀ z) (hx : IsConj a x) (hy : IsConj a y) (hxQ : x ∈ leechQ z)
    (hyQ : y ∈ leechQ z) : (twoAGraph a).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨L⟩ := S365.exists_leechSystem_of_isConj hG hz
  have hT : ∀ {q : G}, q ∈ leechQ z → IsConj a q → L.vec q ∈ co1Orbit 0 := fun hq hqa =>
    (S365.mem_typeSet_zero_of_isConj I hG hz L hq hqa).2
  have hadj : ∀ {p q : G} (hp : IsConj a p) (hq : IsConj a q), p ∈ leechQ z → q ∈ leechQ z →
      L.vec p + L.vec q ∈ co1Orbit 0 → (twoAGraph a).Adj ⟨p, hp⟩ ⟨q, hq⟩ := by
    intro p q hp hq hpQ hqQ hsum
    refine ⟨fun h => ?_, S365.isConj_of_mem_typeSet_zero I hG hz L
      ((L.mul_mem_typeSet_iff hpQ hqQ).2 hsum)⟩
    have hpq : p = q := congrArg Subtype.val h
    subst hpq
    rw [CFSG.Sporadic.Co1.Module.vec_add_self] at hsum
    exact Leech.ne_zero_of_mem_co1Orbit hsum rfl
  rcases ASegConn.co1_diam (hT hxQ hx) (hT hyQ hy) with h | ⟨w, hw, hxw, hyw⟩
  · exact (hadj hx hy hxQ hyQ h).reachable
  · obtain ⟨q, hqQ, hqv⟩ := L.vec_surj w
    have hqT : q ∈ L.typeSet 0 := ⟨hqQ, by rw [hqv]; exact hw⟩
    have hq : IsConj a q := S365.isConj_of_mem_typeSet_zero I hG hz L hqT
    exact (hadj hx hq hxQ hqQ (by rw [hqv]; exact hxw)).reachable.trans
      (hadj hq hy hqQ hyQ (by rw [hqv, add_comm]; exact hyw)).reachable

theorem twoAGraph_preconnected
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    (twoAGraph a).Preconnected :=
  twoAGraph_preconnected_of I hG fun _ hz _ _ hx hy hxQ hyQ =>
    twoAGraph_reachable_of_mem_leechQ I hG hz hx hy hxQ hyQ

end Main

end CFSG.Monster.GMS

module

public import CFSG.RankThree.GF2n.Tim77.Sec51Nonab
public import CFSG.RankThree.GF2n.Tim77.Sec51Abel

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

namespace Sec51Bad

variable [Finite G] {A Abar S₀ B S : Subgroup G} {h a b : G}

theorem false_of_bad
    (H : Sec51Bad A Abar S₀ B S h a b) : False := by
  by_cases hL : Abar ⊓ normalizer (conjSubgroup a Abar : Set G) = Abar
  · have hAbN : Abar ≤ normalizer (conjSubgroup a Abar : Set G) := fun x hx => by
      rw [← hL] at hx
      exact (Subgroup.mem_inf.mp hx).2
    have hcomm' := sec51_comm_of_le_normalizer (isElemAbelian_conj H.ctx.setup.elem_Ab a)
      (isTI_conjSubgroup H.ctx.setup.ti_Ab a) (sec51_conj_of_conj (k := a) rfl) hAbN
    exact sec51_abelian_contra H.ctx H.hq H.tr_a H.ha2 H.conj_a_ne
      fun x hx y hy => (hcomm' y hy x hx).symm
  · exact H.nonab_false (H.prop24_nonab hL)

end Sec51Bad

theorem sec51_holds :
    Tim77Sec51Statement := by
  intro G _ _ A Abar S₀ B h hq _ S hS hSN _ hAb0S
  refine sec51_dih_reduce hS hAb0S (sec51_isElemAbelian_of_le h.setup.elem_Ab h.setup.Lb_le) ?_
  rintro ⟨hh, hhS, a, ha, b, hb, ha2, hb2, hord⟩
  exact Sec51Bad.false_of_bad ⟨h, hq, hS, hSN, hAb0S, hhS, ha, hb, ha2, hb2, hord⟩

end CFSG.RankThree.GF2n.Tim77

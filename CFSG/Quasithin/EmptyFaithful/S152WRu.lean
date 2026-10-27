module

public import CFSG.Quasithin.EmptyFaithful.S152WBase
public import CFSG.GH74.Generic.S45.LSporRu

public section

namespace CFSG.Quasithin.S152W

open CFSG.Blueprint CFSG.Sporadic.RuSchreier CFSG.GH74.Generic.S45

theorem atlasClauses_ruP :
    AtlasClauses ruP := by
  refine atlasClauses_of_data (by rw [card_outer_ruP]; norm_num) [245760, 116480] ?_
    (hbad_of_not_dvd _ (by decide))
  intro t ht
  rw [card_centralizer_subtype]
  have := ru_card_centralizer_involution (t := (t : Equiv.Perm (Fin 4060))) t.2
    (by rw [Subgroup.orderOf_coe]; exact ht)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact this

theorem atlasClauses_Ru :
    AtlasClauses NativeSporadic.Ru :=
  AtlasClauses.of_equiv ruEquivP atlasClauses_ruP

end CFSG.Quasithin.S152W

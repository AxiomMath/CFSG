module

public import CFSG.Quasithin.EmptyFaithful.S146zYFSBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Blueprint CFSG.QuasithinUnique.Ch1.SporLat.Ru

theorem facts134Five_ru :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru) := by
  rintro A _ _ L P T ⟨e⟩ hcfg
  have hL : Nat.card L = 2 ^ 14 * 8906625 := by
    rw [Nat.card_congr e.toEquiv]
    exact (CFSG.Sporadic.Ru.card_Ru).trans (by norm_num)
  obtain ⟨S, Y, hS, hSY, -, hY⟩ := hcfg.exists_sylow_le_of_card (by norm_num) hL
  rcases ru_overgroups ⟨e⟩ hS hSY with htop | ⟨m, hm, hord, -, -⟩
  · rw [htop, Subgroup.card_top, hL] at hY
    norm_num at hY
  · rw [hord] at hY
    simp only [ruMems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num at hY

end CFSG.Quasithin.S146zY

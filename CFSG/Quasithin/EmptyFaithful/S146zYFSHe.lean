module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public import CFSG.Quasithin.EmptyFaithful.S146zYFSBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Blueprint CFSG.QuasithinUnique.Ch1.SporLat.He

theorem facts134Five_he :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .He) := by
  rintro A _ _ L P T ⟨e⟩ hcfg
  have hL : Nat.card L = 2 ^ 10 * 3935925 := by
    rw [Nat.card_congr e.toEquiv]
    exact (CFSG.Sporadic.He.card_He).trans (by norm_num)
  obtain ⟨S, Y, hS, hSY, -, hY⟩ := hcfg.exists_sylow_le_of_card (by norm_num) hL
  rcases he_overgroups ⟨e⟩ hS hSY with htop | ⟨m, hm, hord, -, -⟩
  · rw [htop, Subgroup.card_top, hL] at hY
    norm_num at hY
  · rw [hord] at hY
    simp only [heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hY

end CFSG.Quasithin.S146zY

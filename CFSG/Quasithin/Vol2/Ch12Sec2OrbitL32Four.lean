module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Vol2.Ch10SecD31D

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin

theorem l32FourSylowFix : L32FourSylowFix := by
  intro V _ _ hV hcard H hcomm hnat S hSH hS8
  obtain ⟨D⟩ := hnat.toL3Coord
  have h16 : Nat.card V = 16 := by rw [hcard]; norm_num
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcomm h16
  obtain ⟨-, -, hsyl, -⟩ := B4_8_2 hV h16 hnat hind
  refine hsyl S ⟨hSH, IsPGroup.of_card (n := 3) (by rw [hS8]; norm_num), ?_⟩
  have h1 := (S.subgroupOf H).index_mul_card
  have h2 : Nat.card ↥(S.subgroupOf H) = 8 := by
    rw [← hS8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  rw [h2, D.card_G] at h1
  have h21 : (S.subgroupOf H).index = 21 := by omega
  rw [h21]
  decide

end CFSG.Quasithin.H13.Orbit

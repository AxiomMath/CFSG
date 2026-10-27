module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamQ
import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowON

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

namespace Hering129C

theorem not_twentySeven_dvd_M11 :
    ¬ 27 ∣ Nat.card NativeSporadic.M11 := by
  rw [CFSG.Sporadic.Mathieu.card_M11]
  norm_num

theorem not_twentySeven_dvd_M22 :
    ¬ 27 ∣ Nat.card NativeSporadic.M22 := by
  rw [CFSG.Sporadic.Mathieu.card_M22]
  norm_num

theorem not_twentySeven_dvd_M23 :
    ¬ 27 ∣ Nat.card NativeSporadic.M23 := by
  rw [CFSG.Sporadic.Schreier.m23_card]
  norm_num

theorem not_twentySeven_dvd_J1 :
    ¬ 27 ∣ Nat.card NativeSporadic.J1 := by
  rw [CFSG.Sporadic.J1.card_J1]
  norm_num

theorem not_twentySeven_dvd_HS :
    ¬ 27 ∣ Nat.card NativeSporadic.HS := by
  rw [CFSG.Sporadic.HS.card_HS]
  norm_num

theorem kFCensus46Five_order :
    KFCensusOn (fun Q _ => ∃ s ∈ ([.M11, .M22, .M23, .J1, .HS] : List TauCeti.SporadicName),
      Nonempty (Q ≃* NativeSporadic.Carrier s)) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨s, hs, ⟨e⟩⟩ := hQ
  refine (ppair_self hD).false_of_not_dvd ?_
  rw [Nat.card_congr e.toEquiv]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact not_twentySeven_dvd_M11
  · exact not_twentySeven_dvd_M22
  · exact not_twentySeven_dvd_M23
  · exact not_twentySeven_dvd_J1
  · exact not_twentySeven_dvd_HS

theorem kFCensus46Five_cover_M22 :
    KFCensusOn (fun Q _ => Sec4.IsExtOf Q (NativeSporadic.Carrier .M22)
      (Multiplicative (ZMod 3))) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨s, J, g, hg⟩ := ppair_of_census_ext hD hQ
  haveI := finite_of_isExtOf hQ
  exact hg.false_of_not_dvd not_twentySeven_dvd_M22

theorem kFCensus46Five_cover_ON :
    KFCensusOn (fun Q _ => Sec4.IsExtOf Q (NativeSporadic.Carrier .ONan)
      (Multiplicative (ZMod 3))) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨s, J, g, hg⟩ := ppair_of_census_ext hD hQ
  haveI := finite_of_isExtOf hQ
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact hg.false_of_abelian_sylow (Sec4.Ronan148S.sylow_three_comm_of_ON β)

end Hering129C

end CFSG.RankThree.PartTwo.Sec12

module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamQ
import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowJ3McL

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

namespace Hering129C

section McL


theorem PPair.false_McL {Lb : Type} [Group Lb] {s : NativeSporadic.Carrier .McL}
    {J : Subgroup (NativeSporadic.Carrier .McL)} {g : ↥J →* Lb}
    [Finite (NativeSporadic.Carrier .McL)] (h : PPair s J g) : False := by
  have hC : Nat.card (Subgroup.centralizer ({s} : Set (NativeSporadic.Carrier .McL))) ∣ 29160 := by
    rcases KFacts.K426Rest.mclThreeCentralizerCard s h.orderOf_s with h' | h'
    · exact dvd_of_eq h'
    · exact (dvd_of_eq h').trans (by norm_num)
  exact h.false_of_noA6 (B := 31) (by norm_num) (by norm_num) (by decide +kernel) hC
    fun H hH f => KFacts.K426.mclThreeCentralizer s h.orderOf_s H hH f

theorem kFCensus46Five_McL :
    KFCensusOn (fun Q _ => Nonempty (Q ≃* NativeSporadic.Carrier .McL)) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨e⟩ := hQ
  haveI : Finite (NativeSporadic.Carrier .McL) := Finite.of_equiv Q e.toEquiv
  obtain ⟨g, hg⟩ := (ppair_self hD).map e
  exact hg.false_McL

theorem kFCensus46Five_cover_McL :
    KFCensusOn (fun Q _ => Sec4.IsExtOf Q (NativeSporadic.Carrier .McL)
      (Multiplicative (ZMod 3))) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨s, J, g, hg⟩ := ppair_of_census_ext hD hQ
  haveI := finite_of_isExtOf hQ
  exact hg.false_McL

end McL

section J3


theorem PPair.false_J3 {Lb : Type} [Group Lb] {s : NativeSporadic.Carrier .J3}
    {J : Subgroup (NativeSporadic.Carrier .J3)} {g : ↥J →* Lb}
    [Finite (NativeSporadic.Carrier .J3)] (h : PPair s J g) : False := by
  rcases Sec21.Item228CensusProof.j3ThreeCentralizerCard s h.orderOf_s with hC | hC
  · refine h.false_of_card_eq (B := 11) hC (by norm_num) (by norm_num) (by decide +kernel) ?_
    intro hc
    have hle := Sec4.Ronan148S.card_comm_J3_le s h.orderOf_s hC
    rw [hc, hC] at hle
    norm_num at hle
  · exact h.false_of_card_dvd (M := 243) (B := 7) (by norm_num) (by norm_num)
      (by decide +kernel) (dvd_of_eq hC)

theorem kFCensus46Five_J3 :
    KFCensusOn (fun Q _ => Nonempty (Q ≃* NativeSporadic.Carrier .J3)) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨e⟩ := hQ
  haveI : Finite (NativeSporadic.Carrier .J3) := Finite.of_equiv Q e.toEquiv
  obtain ⟨g, hg⟩ := (ppair_self hD).map e
  exact hg.false_J3

theorem kFCensus46Five_cover_J3 :
    KFCensusOn (fun Q _ => Sec4.IsExtOf Q (NativeSporadic.Carrier .J3)
      (Multiplicative (ZMod 3))) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨s, J, g, hg⟩ := ppair_of_census_ext hD hQ
  haveI := finite_of_isExtOf hQ
  exact hg.false_J3

end J3

end Hering129C

end CFSG.RankThree.PartTwo.Sec12

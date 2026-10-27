module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumDef

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

theorem false_of_fixedDatum_cyclic {F : Type} [Group F] [IsCyclic F] (h : FixedDatum F) :
    False := by
  obtain ⟨R, P, -, -, hPnc, -, -⟩ := h
  exact hPnc inferInstance

theorem false_of_fixedDatum_odd {F : Type} [Group F] [Finite F] (hF : Odd (Nat.card F))
    (h : FixedDatum F) : False := by
  obtain ⟨R, P, -, hP2, hPnc, -, -⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hP2.card_eq_or_dvd with h1 | h2
  · apply hPnc
    haveI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · exact (Nat.not_even_iff_odd.mpr hF) (even_iff_two_dvd.mpr (dvd_trans h2
      (Subgroup.card_subgroup_dvd_card P)))

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end

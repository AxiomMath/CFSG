module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Cases
import CFSG.RankThree.PartTwo.Sec19.SimsC198PSL2
import CFSG.RankThree.PartTwo.Sec19.SimsC198Alt
import CFSG.RankThree.PartTwo.Sec19.SimsC198Iso

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem caseHolds_one : CaseHolds Alt42One := by
  intro X _ _ _ c L 𝒟 hD h
  obtain ⟨p, e, _, -, -, ⟨φ⟩⟩ := h
  exact absurd hD ((NoLocalDatum.of_mulEquiv φ
    (noLocalDatum_projSL_two (GaloisField p e))).noAutDatum c L 𝒟)

theorem noLocalDatum_alternatingGroup {n : ℕ} (hn : n ≤ 14) :
    NoLocalDatum (alternatingGroup (Fin n)) := fun c L h =>
  alternating_false_of_perfect_centralizer hn c h.orderOf_eq L h.le_centralizer h.mem h.perfect

theorem caseHolds_five : CaseHolds Alt42Five := by
  intro X _ _ _ c L 𝒟 hD h
  obtain ⟨n, -, hn, ⟨φ⟩⟩ := h
  exact absurd hD ((NoLocalDatum.of_mulEquiv φ
    (noLocalDatum_alternatingGroup (by omega))).noAutDatum c L 𝒟)

end CFSG.RankThree.PartTwo.Sec19.SimsC198

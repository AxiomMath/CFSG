module

public import CFSG.RankThree.PartOne.S9.Extraction.InvariantSylow
public import CFSG.RankThree.PartOne.S9.Extraction.Tail
public import CFSG.RankThree.PartOne.S9.StatementsSylow

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.PartOne.Extract CFSG.RankThree.LocalRank

theorem initialCriticalAction : InitialCriticalAction := by
  intro H _ _ p hp hp2 A T hAe hA3 hT hAT hTA
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSs, -, hpS, -, -, -, hScore⟩ :=
    solvable_prime_complement_core_characterization (H := H) hp
  have hJS : pCore 2 H ≤ aschbacherSolvableCore p H :=
    hScore 2 Nat.prime_two (Ne.symm hp2)
  have hJeq : pCore 2 H = inSubgroup (pCore 2) (aschbacherSolvableCore p H) := by
    rw [inSubgroup_pCore_eq_inf, inf_eq_right.mpr hJS]
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  obtain ⟨q, hq, hq2, hqp, R, Q, hRT, hAR, hRc, hRJ, hRmin, hQ, hRQ, hAQ, hRQ'⟩ :=
    invariantSylowOddActionExtraction H p hp hp2 A (aschbacherSolvableCore p H) T hAp inferInstance
      hSs hpS hJeq hT hAT hTA
  have hR2 : IsPGroup 2 R := hT.2.1.to_le hRT
  obtain ⟨D, hDQ, hDchar, hDne, hRD, hDexp, hDQ', hRD', hcard, hC⟩ :=
    critical_tail hp2 hq hq2 hA3 inferInstance hpS (hRT.trans hT.1) hR2 hAR hRc hRJ hRmin hQ.2.1
      hRQ hRQ'
  exact ⟨q, hq, hq2, hqp, R, Q, D, hRT, hAR, hRc, hRJ, hRD', hQ, hRQ, hAQ, hDQ, hDchar, hDne,
    hRD, hDexp, hDQ', hcard, hC⟩

end CFSG.RankThree.PartOne

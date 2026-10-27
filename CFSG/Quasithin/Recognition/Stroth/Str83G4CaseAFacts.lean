module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAFact5

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem caseA_iff_five_le_b
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    str83R L1 L2 S ≤ Q1 L1 L2 S ↔ 5 ≤ caseAB L1 L2 S := by
  constructor
  · intro hA
    have h4 : 4 < caseAB L1 L2 S :=
      (caseA_boundAt_iff_lt hfr).mp (caseA_boundAt_four hfr hA)
    omega
  · intro h
    exact (caseA_boundAt_three_iff hfr).mp ((caseA_boundAt_iff_lt hfr).mpr (by omega))

end CFSG.Quasithin.Stroth

end

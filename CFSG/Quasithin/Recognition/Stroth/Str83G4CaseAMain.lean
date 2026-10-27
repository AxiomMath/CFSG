module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAEvenC
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAFacts
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAOddB

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem caseA_false
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) : False := by
  have hb5 : 5 ≤ caseAB L1 L2 S := (caseA_iff_five_le_b hfr).mp hA
  obtain ⟨hball, β, δ, hβ, hd, hnot⟩ := caseAB_spec hfr
  obtain ⟨x, hx, -⟩ := caseA_critPath_of_pair hball hβ hd hnot
  rcases Nat.even_or_odd (caseAB L1 L2 S) with he | ho
  · exact caseA_even_false hfr hA hx he hb5
  · exact caseA_odd_false hfr hA hx ho hb5

theorem str83G4CaseAFalse_of_caseA :
    Str83G4CaseAFalse :=
  fun _ _ _ _ _ _ _ hfr hA => caseA_false hfr hA

end CFSG.Quasithin.Stroth

end

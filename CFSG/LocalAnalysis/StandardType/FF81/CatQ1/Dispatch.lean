module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs

public section

namespace CFSG.StandardType.FF81.CatQ1

open TauCeti

theorem outerThreeBigAt_of_families
    (hA : OuterThreeBigAt (fun i => ∃ r q, i = .A r q))
    (htA : OuterThreeBigAt (fun i => ∃ r q, i = .twistedA r q))
    (hB2 : OuterThreeBigAt (fun i => ∃ q, i = .B 2 q))
    (hBe : OuterThreeBigAt (fun i => ∃ r q, i = .B r q ∧ q.p = 2 ∧ 3 ≤ r))
    (hBo : OuterThreeBigAt (fun i => ∃ r q, i = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r))
    (hC : OuterThreeBigAt (fun i => ∃ r q, i = .C r q))
    (hD4 : OuterThreeBigAt (fun i => ∃ q, i = .D 4 q))
    (hD : OuterThreeBigAt (fun i => ∃ r q, i = .D r q ∧ 5 ≤ r))
    (htD : OuterThreeBigAt (fun i => ∃ r q, i = .twistedD r q))
    (hE6 : OuterThreeBigAt (fun i => ∃ q, i = .E6 q))
    (hE7 : OuterThreeBigAt (fun i => ∃ q, i = .E7 q))
    (hE8 : OuterThreeBigAt (fun i => ∃ q, i = .E8 q))
    (hF4 : OuterThreeBigAt (fun i => ∃ q, i = .F4 q))
    (hG2 : OuterThreeBigAt (fun i => ∃ q, i = .G2 q))
    (htE6 : OuterThreeBigAt (fun i => ∃ q, i = .twistedE6 q))
    (hT : OuterThreeBigAt (fun i => ∃ q, i = .trialityD4 q))
    (hSz : OuterThreeBigAt (fun i => ∃ m, i = .suzuki m))
    (hRG : OuterThreeBigAt (fun i => ∃ m, i = .reeG2 m))
    (hRF : OuterThreeBigAt (fun i => ∃ m, i = .reeF4 m))
    (hTits : OuterThreeBigAt (fun i => i = .tits)) :
    OuterThreeBigAt (fun _ => True) := by
  rintro K _ _ ⟨i, hv⟩ - he
  have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases i with
  | A r q => exact hA K ⟨_, hv⟩ ⟨r, q, rfl⟩ he
  | twistedA r q => exact htA K ⟨_, hv⟩ ⟨r, q, rfl⟩ he
  | B r q =>
    by_cases hr2 : r = 2
    · subst hr2
      exact hB2 K ⟨_, hv⟩ ⟨q, rfl⟩ he
    · have hr3 : 3 ≤ r := by have := hr.1; omega
      by_cases hp : q.p = 2
      · exact hBe K ⟨_, hv⟩ ⟨r, q, rfl, hp, hr3⟩ he
      · exact hBo K ⟨_, hv⟩ ⟨r, q, rfl, hp, hr3⟩ he
  | C r q => exact hC K ⟨_, hv⟩ ⟨r, q, rfl⟩ he
  | D r q =>
    by_cases hr4 : r = 4
    · subst hr4
      exact hD4 K ⟨_, hv⟩ ⟨q, rfl⟩ he
    · have hr5 : 5 ≤ r := by omega
      exact hD K ⟨_, hv⟩ ⟨r, q, rfl, hr5⟩ he
  | twistedD r q => exact htD K ⟨_, hv⟩ ⟨r, q, rfl⟩ he
  | E6 q => exact hE6 K ⟨_, hv⟩ ⟨q, rfl⟩ he
  | E7 q => exact hE7 K ⟨_, hv⟩ ⟨q, rfl⟩ he
  | E8 q => exact hE8 K ⟨_, hv⟩ ⟨q, rfl⟩ he
  | F4 q => exact hF4 K ⟨_, hv⟩ ⟨q, rfl⟩ he
  | G2 q => exact hG2 K ⟨_, hv⟩ ⟨q, rfl⟩ he
  | twistedE6 q => exact htE6 K ⟨_, hv⟩ ⟨q, rfl⟩ he
  | trialityD4 q => exact hT K ⟨_, hv⟩ ⟨q, rfl⟩ he
  | suzuki m => exact hSz K ⟨_, hv⟩ ⟨m, rfl⟩ he
  | reeG2 m => exact hRG K ⟨_, hv⟩ ⟨m, rfl⟩ he
  | reeF4 m => exact hRF K ⟨_, hv⟩ ⟨m, rfl⟩ he
  | tits => exact hTits K ⟨_, hv⟩ rfl he

end CFSG.StandardType.FF81.CatQ1

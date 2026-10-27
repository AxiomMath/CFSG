module

public import CFSG.Sporadic.Recognition.J3Multiplier
public import Certificates.Certificate24090
public import Certificates.Certificate24091

public section

namespace CFSG.Sporadic.Recognition.J3Multiplier

open CFSG.Sporadic.J3.Native (j3Data)
open CFSG.Sporadic.Bridge.TwoGen.Native
open CFSG.Monster.Schur

theorem relCheck_eq_true :
    j3RelCheck j3Data natWords = true :=
  Certificates.certificate24090

theorem noPerfectDoubleCover_J_of_certificate :
    NoPerfectDoubleCover (CFSG.Sporadic.J3.J j3Data) := by
  obtain ⟨h0, hε⟩ := Certificates.certificate24091
  refine noPerfectDoubleCover_of_eps_cases (m := 2) (k := 2) gen closure_gen U T
    (exists_lifts relCheck_eq_true) (lift_gen_T relCheck_eq_true) ?_ ?_
  · exact ⟨h0.1, h0.2.trans card_J.ge⟩
  · intro e he
    exact ⟨(hε e he).1, (hε e he).2.trans card_J.ge⟩

theorem noPerfectDoubleCover_nativeJ3_of_certificate :
    NoPerfectDoubleCover CFSG.Blueprint.NativeSporadic.J3 :=
  @NoPerfectDoubleCover.of_mulEquiv (CFSG.Sporadic.J3.J j3Data) _ _ _
    CFSG.Sporadic.Bridge.J3.nativeEquiv.symm noPerfectDoubleCover_J_of_certificate

end CFSG.Sporadic.Recognition.J3Multiplier

module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedAOne
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedAHigher
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedTwistedA
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedC
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedD
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedBEven
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedBOdd
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedBTwo
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedE6
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedE78
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedExcTwisted
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedF4G2
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedTits
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedTwistedD
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOutProvedTwistedE6

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_of_ne_tits
    (d : TauCeti.ValidLieTypeIndex) (hne : d.1 ≠ .tits) (J : Type) [Group J] [Finite J]
    (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  have hrange := ((TauCeti.LieTypeIndex.valid_iff d').1 hv).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
  cases d' with
  | A n q =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by have := hrange.1; omega
      exact tmOut_A_one ⟨.A 1 q, hv⟩ q rfl J e
    · exact tmOut_A_higher ⟨.A n q, hv⟩ n q rfl h J e
  | twistedA n q => exact tmOut_twistedA ⟨.twistedA n q, hv⟩ n q rfl J e
  | B n q =>
    by_cases hp : q.p = 2
    · rcases Nat.lt_or_ge n 3 with h | h
      · obtain rfl : n = 2 := by have := hrange.1; omega
        exact tmOut_B_two_even ⟨.B 2 q, hv⟩ q rfl hp J e
      · exact tmOut_B_even ⟨.B n q, hv⟩ n q rfl h hp J e
    · exact tmOut_B_odd ⟨.B n q, hv⟩ n q rfl hp J e
  | C n q => exact tmOut_C ⟨.C n q, hv⟩ n q rfl J e
  | tits => exact absurd rfl hne
  | D n q => exact tmOut_D ⟨.D n q, hv⟩ n q rfl J e
  | twistedD n q => exact tmOut_twistedD ⟨.twistedD n q, hv⟩ n q rfl J e
  | E6 q => exact tmOut_E6 ⟨.E6 q, hv⟩ q rfl J e
  | E7 q => exact tmOut_E7 ⟨.E7 q, hv⟩ q rfl J e
  | E8 q => exact tmOut_E8 ⟨.E8 q, hv⟩ q rfl J e
  | F4 q => exact tmOut_F4 ⟨.F4 q, hv⟩ q rfl J e
  | G2 q => exact tmOut_G2 ⟨.G2 q, hv⟩ q rfl J e
  | twistedE6 q => exact tmOut_twistedE6 ⟨.twistedE6 q, hv⟩ q rfl J e
  | trialityD4 q => exact tmOut_trialityD4 ⟨.trialityD4 q, hv⟩ q rfl J e
  | suzuki m => exact tmOut_suzuki ⟨.suzuki m, hv⟩ m rfl J e
  | reeG2 m => exact tmOut_reeG2 ⟨.reeG2 m, hv⟩ m rfl J e
  | reeF4 m => exact tmOut_reeF4 ⟨.reeF4 m, hv⟩ m rfl J e

theorem tmLieOutAll_holds :
    TmLieOutAll := by
  intro d J _ _ e
  by_cases ht : d.1 = .tits
  · exact tmOut_tits d ht J e
  · exact tmOut_of_ne_tits d ht J e

end CFSG.StandardType.FrameRoute

end

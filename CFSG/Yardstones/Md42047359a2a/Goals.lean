module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporMathieuLeech
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporPariah
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporMonsterSection
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestB
import CFSG.HardMathSupport.Dickson.ElementCaseBp.Main
import CFSG.HardMathSupport.Dickson.OddLieB2.Assembly
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Assembly
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Final
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.Assembly
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblySO
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyExc
public import CFSG.HardMathSupport.Solomon.Coordinator.B2LieEven

public section

namespace CFSG.Yardstones.Md42047359a2a

open CFSG.HardMathSupport.Solomon.Coordinator

theorem alternatingTwoBp_holds : AlternatingTwoBp := by
  intro n hn S _ _ _ _ ⟨e⟩ β hβ
  exact B2FamAlt.commutator_layer_eq_bot_two hn e β hβ

theorem sporadicMathieuLeechBp_holds :
    SporadicMathieuLeechBp :=
  b3SporPair_mathieuLeech

theorem sporadicMonsterSectionBp_holds :
    SporadicMonsterSectionBp :=
  b3SporPair_monsterSection_of
    (b3SporPair_B_seven CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds)

theorem sporadicPariahBp_holds :
    SporadicPariahBp :=
  b3SporPair_pariah

theorem lieSemisimpleCentLinearUnitary_holds : LieSemisimpleCentLinearUnitary :=
  LieSemisimple.lieSemisimpleCentLinearUnitary

theorem lieSemisimpleCentSymplecticOrthogonal_holds :
    LieSemisimpleCentSymplecticOrthogonal :=
  LieSemisimple.lieSemisimpleCentSymplecticOrthogonal

theorem lieSemisimpleCentExceptional_holds :
    LieSemisimpleCentExceptional :=
  LieSemisimple.lieSemisimpleCentExceptional

theorem lieSemisimpleCentSuzukiReeTits_holds :
    LieSemisimpleCentSuzukiReeTits :=
  CFSG.HardMathSupport.Dickson.SuzukiReeB.lieSemisimpleCentSuzukiReeTits

theorem lieDefCharOuter_holds :
    LieDefCharOuter :=
  CFSG.HardMathSupport.Dickson.DefCharOuter.lieDefCharOuter

theorem lieClassicalOddCharTwoBp_holds : LieClassicalOddCharTwoBp :=
  CFSG.HardMathSupport.Dickson.OddLieB2.lieClassicalOddCharTwoBp

theorem lieExceptionalOddCharTwoBp_holds :
    LieExceptionalOddCharTwoBp :=
  CFSG.HardMathSupport.Dickson.OddLieB2.lieExceptionalOddCharTwoBp

theorem lieEvenCharTwoBp_holds :
    LieEvenCharTwoBp := by
  intro idx hchar S _ _ hS hnc he β hβ
  exact B2FamAlt.lieEvenCharTwoBp idx hchar S hS hnc he β hβ

theorem elementCaseBp_holds : ElementCaseBp :=
  CFSG.HardMathSupport.Dickson.ElementCaseBp.elementCaseBp

end CFSG.Yardstones.Md42047359a2a

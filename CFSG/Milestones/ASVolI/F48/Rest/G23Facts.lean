
module


public import Certificates.Certificate7761
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates

attribute [local irreducible] burnsideF48t_g23LArr burnsideF48t_g23Tau burnsideF48t_g23GensArr
  burnsideF48t_g23PtsStr

section Chains

theorem burnsideF48t_g23_card_X : Nat.card ↥burnsideF48t_g23X = 4245696 :=
  Certificates.certificate7761.1

theorem burnsideF48t_g23_card_B' : Nat.card ↥burnsideF48t_g23B' = 2916 :=
  Certificates.certificate7761.2.2.2.1

theorem burnsideF48t_g23_card_S0' : Nat.card ↥burnsideF48t_g23S0' = 729 :=
  Certificates.certificate7761.2.2.2.2.1

theorem burnsideF48t_g23_card_K' : Nat.card ↥burnsideF48t_g23K' = 4 :=
  Certificates.certificate7761.2.2.2.2.2

end Chains

end CFSG.ASVolI

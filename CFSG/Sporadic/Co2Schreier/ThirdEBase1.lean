
module

public import CFSG.Sporadic.Co2Schreier.ThirdEBase

public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase1
public import CFSG.Sporadic.Co2Schreier.Action
public import CFSG.Sporadic.Co2Schreier.Cores
public import CFSG.Sporadic.Co2Schreier.Kernel
public import CFSG.Sporadic.Co2Schreier.SylowLemmas
public import CFSG.Sporadic.Schreier.RuSylowB
public import Certificates.Certificate2062
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs
public import Certificates.Certificate2062Base

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.RuSchreier
  CFSG.Sporadic.SmallF2.Native

theorem thirdBase_nodup : witRec.third.baseIndices.Nodup :=
  Certificates.certificate2062.1

theorem thirdBase_lt : ∀ x ∈ witRec.third.baseIndices, x < 2300 :=
  Certificates.certificate2062.2

end CFSG.Sporadic.Co2Schreier

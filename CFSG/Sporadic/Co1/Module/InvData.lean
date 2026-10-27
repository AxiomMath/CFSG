
module

public import CFSG.Sporadic.Co1.Module.InvDataBase

public import CFSG.Sporadic.Co1.Module.InvGroup
public import CFSG.Sporadic.Co1.Module.InvDataInputs
public import Certificates.Certificate10070
public import CFSG.Sporadic.Co1.Module.InvFamInputs
public meta import CFSG.Sporadic.Co1.Module.FormsBase1
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public import Certificates.Certificate10070Base

public section

set_option Elab.async false

namespace CFSG.Sporadic.Co1.Module

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative

theorem repOK_A : repOK kGens kGensInv rowsSA code3 = true :=
  Certificates.certificate10070.1

theorem repOK_B : repOK nGens nGensInv rowsSB code4 = true :=
  Certificates.certificate10070.2.1

theorem repOK_C : repOK nGens nGensInv rowsSC code4 = true :=
  Certificates.certificate10070.2.2.1

theorem counts_A : countsOK rowsSA 65536 30720 = true :=
  Certificates.certificate10070.2.2.2.1

theorem counts_B : countsOK rowsSB 4096 0 = true :=
  Certificates.certificate10070.2.2.2.2.1

theorem counts_C : countsOK rowsSC 4096 2048 = true :=
  Certificates.certificate10070.2.2.2.2.2.1

theorem conj_ok : ∃ W : InvFamW, InvFamOK W :=
  Certificates.certificate10070.2.2.2.2.2.2.1

theorem q0_code3 : q0N (transposeRows 24 qRows) code3 = true :=
  Certificates.certificate10070.2.2.2.2.2.2.2.1

theorem wit_A :
    witOK [false, false, false, false] rowsSA rowsSA 3 = true :=
  Certificates.certificate10070.2.2.2.2.2.2.2.2.1

theorem wit_B : witOK [false] rowsSA rowsSB 10 = true :=
  Certificates.certificate10070.2.2.2.2.2.2.2.2.2.1

theorem wit_C :
    witOK [true, true, true, false] rowsSA rowsSC 12 = true :=
  Certificates.certificate10070.2.2.2.2.2.2.2.2.2.2.1

theorem q0_code4 : q0N (transposeRows 24 qRows) code4 = false :=
  Certificates.certificate10070.2.2.2.2.2.2.2.2.2.2.2.1

theorem code4_word :
    vecMulN 24 (transposeRows 24 (wordRows code4Word)) 1 = code4 :=
  Certificates.certificate10070.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.Co1.Module

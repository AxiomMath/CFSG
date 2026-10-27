module

public import CFSG.Sporadic.Co2Smith.Cat
public import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import Certificates.Data.CFSGNative.Co2Smith.Check
public import CFSG.Sporadic.Co2Smith.CheckInputs
public import Certificates.Certificate10080
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public meta import Certificates.Data.CFSGNative.Co2Smith.Check
public import CFSG.Certificates.InvariantMerge

set_option compiler.extract_closed false

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert

theorem class_check : Native.classOK seedRowsArr = true :=
  Certificates.certificate10080.2.1

theorem elements_check : Native.elementsOK seedRowsArr = true :=
  Certificates.certificate10080.2.2.1

theorem pair_check : Native.pairOK seedRowsArr = true :=
  Certificates.certificate10080.2.2.2.1

theorem chain_check : Native.chainOK seedRowsArr = true :=
  Certificates.certificate10080.2.2.2.2.1

theorem frame_check : Native.frameOK seedRowsArr = true :=
  Certificates.certificate10080.2.2.2.2.2.1

theorem zeta_check : Native.zetaOK seedRowsArr = true :=
  Certificates.certificate10080.2.2.2.2.2.2.1

theorem xFpf_check : Native.xFpfOK seedRowsArr = true :=
  Certificates.certificate10080.2.2.2.2.2.2.2.1

theorem res_check : Native.resOK seedRowsArr = true :=
  Certificates.certificate10080.2.2.2.2.2.2.2.2

end CFSG.Sporadic.Co2Smith

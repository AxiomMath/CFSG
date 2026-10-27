
module

public import CFSG.Sporadic.Fi22.LocalCertBase

public import Certificates.Data.CFSGNative.Fi22.Local
public meta import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb
public import Certificates.Certificate1009
public import Certificates.Certificate1009Base

public section

namespace CFSG.Sporadic.Fi22

open Native CFSG.Perm.Native CFSG.F4.Native

theorem local_certificate :
    (uPtsOK && chainOK 693 t46Letters t46Base t46Q t46Base t46Trees 3 &&
      orbitSizes t46Trees == [693, 512, 120, 36, 6]) = true :=
  Certificates.certificate1009

end CFSG.Sporadic.Fi22


module

public import CFSG.Sporadic.Schreier.J4SCheckBase

public import CFSG.Sporadic.Schreier.J4SNative
public meta import CFSG.Sporadic.Schreier.J4SNative
public meta import Certificates.Data.CFSGNative.J4.Cert
public import CFSG.Sporadic.Schreier.J4SCols
public meta import CFSG.Sporadic.Schreier.J4SCols
public import Certificates.Certificate2168
public import CFSG.Quasithin.H13.J4Words

public section

namespace CFSG.Sporadic.J4Schreier

theorem rootCheck_eq : rootCheck = true :=
  Certificates.certificate2168.1

theorem colsCheck_eq : colsCheck = true :=
  Certificates.certificate2168.2.1

theorem elemCheck_eq : elemCheck = true :=
  Certificates.certificate2168.2.2.1

theorem kset_w_lt : O.vmul ksetVectors[0]! Zn.1 < 2 ^ 112 :=
  Certificates.certificate2168.2.2.2.1

theorem kset_all : ∀ i < ksetSize, ksetVectors[i]! < 2 ^ 112 ∧ (ksetEdges[i]!)[0]! < ksetSize ∧
    ksetVectors[(ksetEdges[i]!)[0]!]! = O.vmul ksetVectors[i]! Xn.1 ∧
    (ksetEdges[i]!)[1]! < ksetSize ∧
    ksetVectors[(ksetEdges[i]!)[1]!]! = O.vmul ksetVectors[i]! Yn.1 ∧
    ksetVectors[i]! ≠ O.vmul ksetVectors[0]! Zn.1 :=
  Certificates.certificate2168.2.2.2.2.1

theorem matChecks_eq : CFSG.Sporadic.J4.Native.matChecks = true :=
  Certificates.certificate2168.2.2.2.2.2.1

theorem matFacts : CFSG.Sporadic.J4.MatFacts := CFSG.Sporadic.J4.matFacts_of matChecks_eq

theorem comp11_x_inv : comp11 xColumns xInvColumns = CFSG.Sporadic.SmallF2.Native.idRows 11 :=
  Certificates.certificate2168.2.2.2.2.2.2.1

theorem comp11_y_inv : comp11 yColumns yInvColumns = CFSG.Sporadic.SmallF2.Native.idRows 11 :=
  Certificates.certificate2168.2.2.2.2.2.2.2

end CFSG.Sporadic.J4Schreier

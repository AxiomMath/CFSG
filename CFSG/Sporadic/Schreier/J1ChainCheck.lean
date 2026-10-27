module

public import CFSG.Sporadic.Schreier.J1CertData
public import CFSG.Monster.B.Mathieu.ChainCheck
public meta import CFSG.Sporadic.Schreier.J1CertData
public meta import CFSG.Monster.B.Mathieu.ChainCheck
public import Certificates.Certificate2165
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu CFSG.Certificates.Native

theorem j1_chain_check : J1Certificate.chain.check 3080 = true :=
  Certificates.certificate2165.1

theorem j1_chain_base : J1Certificate.chain.base = [0, 1, 2] :=
  Certificates.certificate2165.2.1

theorem j1_chain_orbitSizes : J1Certificate.chain.orbitSizes 3080 = [3080, 19, 3] :=
  Certificates.certificate2165.2.2

end CFSG.Sporadic.Schreier

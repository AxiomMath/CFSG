module

public import CFSG.Sporadic.Schreier.Co1CertData
public import CFSG.Sporadic.Schreier.Co1ChainCheck
public import CFSG.Sporadic.Co2Cert.CheckInputs
import Certificates.Certificate2043
import Certificates.Certificate2144
import Certificates.Kernel.Co1B.C2043
import CFSG.Sporadic.Schreier.Co1CertRecData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.Co1Block.Perm
import CFSG.Sporadic.Schreier.Co1QuotCheck
import CFSG.Sporadic.Co2Cert.Cert
import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Sporadic.Schreier.Co1StabLift
public import CFSG.Sporadic.Schreier.Co1Chain
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate3024
public import Certificates.Certificate3115
public import CFSG.Certificates.InvariantMerge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD rowsMatrix)
open CFSG.Monster.B.Co2 (permOfArr Rep rep_permOfArr)
open CFSG.Sporadic.Co2Cert (isPermList isPermList_spec rep_of_isPermList co2Q co2P
  co2Q_originalSubgroup)

@[expose] noncomputable def certVec (i : ℕ) : Vec24 := toVecD 24 (co1Rec.vectors.getD i 0)

@[expose] noncomputable def certX : Set Vec24 := {v | ∃ i < 98280, certVec i = v}

end CFSG.Sporadic.Co1Schreier

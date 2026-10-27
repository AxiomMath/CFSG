module

public import CFSG.Sporadic.HNSchreier.OrbitCheck
public import CFSG.Sporadic.HNSchreier.SeedsCheck
public import Std.Data.HashMap
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.SepCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public import Certificates.Certificate2107

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.F5.Native CFSG.Sporadic.He.Native

theorem level_cert :
    Nat.card (CFSG.Sporadic.F5.J hnsData) = 273030912000000 ∧ LevelFacts :=
  Certificates.certificate2107.2

end CFSG.Sporadic.HNSchreier.Native

namespace CFSG.Sporadic.HNSchreier

open Matrix

theorem form_parts :
    formMᵀ = formM ∧ formM.det ≠ 0 ∧ matAᵀ * formM * matA = formM ∧
    matBᵀ * formM * matB = formM :=
  Certificates.certificate2107.1

end CFSG.Sporadic.HNSchreier

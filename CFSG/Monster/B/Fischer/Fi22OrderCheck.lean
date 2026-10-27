module

public import CFSG.Monster.B.Fischer.PinnedChain
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Monster.B.Fischer.PinnedChain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import Certificates.Certificate3147

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem fi22Order_check :
    rawChainOK 3510 fi22OrigArrs fi22StrongArrs fi22BaseArr fi22WordArrs 4 = true ∧
    rawOrbitSizes 3510 fi22StrongArrs fi22BaseArr = [3510, 2816, 567, 720, 8, 2] :=
  Certificates.certificate3147.1

theorem fi22Orders_check :
    eqA 3510 (powA 3510 (fi22ChainGen 0) 2) (idA 3510) = true ∧
    eqA 3510 (fi22ChainGen 0) (idA 3510) = false ∧
    eqA 3510 (powA 3510 (fi22ChainGen 1) 13) (idA 3510) = true ∧
    eqA 3510 (fi22ChainGen 1) (idA 3510) = false ∧
    eqA 3510 (powA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) 11) (idA 3510) = true ∧
    eqA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) (idA 3510) = false :=
  Certificates.certificate3147.2

end CFSG.Monster.B.Fischer

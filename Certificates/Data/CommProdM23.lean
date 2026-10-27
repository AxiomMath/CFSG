module

public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionData
public meta import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionData
public import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public meta import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23Base
public meta import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M23CheckBase
public meta import CFSG.Sporadic.Schreier.M23CheckBase
public meta import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace Certificates.CommProd

open CFSG.Sporadic.Schreier

@[expose] def commVal {n : ℕ} (S : List (Equiv.Perm (Fin n))) (p : List ℤ × List ℤ) :
    Equiv.Perm (Fin n) :=
  evalCodes S p.1 * evalCodes S p.2 * (evalCodes S p.1)⁻¹ * (evalCodes S p.2)⁻¹

@[expose] def prodComm {n : ℕ} (S : List (Equiv.Perm (Fin n))) :
    List (List ℤ × List ℤ) → Equiv.Perm (Fin n)
  | [] => 1
  | p :: r => commVal S p * prodComm S r

@[expose] def commProdOK {n : ℕ} (S : List (Equiv.Perm (Fin n)))
    (W : List (List (List ℤ × List ℤ))) : Bool :=
  W.length == S.length &&
    (List.range S.length).all fun i => decide (S.getD i 1 = prodComm S (W.getD i []))

@[expose] def m23CentPerfWit : List (List (List ℤ × List ℤ)) := [
    [([2], [-3, -3, -4])],
    [([1], [4, 3, 1, 3])],
    [([1, -4], [4, 3, 4, 2])],
    [([-3, -3], [4, 1, 4, 1])]]

end Certificates.CommProd

module

public import CFSG.Quasithin.Recognition.RuRank3PSLInputs
import Certificates.Kernel.PSL26.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.RuSchreier in
open scoped MatrixGroups Matrix LinearAlgebra.Projectivization in
theorem certificate7044 :
    ruChainOK 26 psl26Strong 3 9 [0, 1, 2] psl26Words = true ∧
      rawOrbitSizes 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) = [26, 25, 12] ∧
      eqA 26 psl26Strong[0]! psl26X = true ∧ eqA 26 psl26Strong[1]! psl26S = true ∧
      eqA 26 psl26Strong[2]! psl26T = true ∧ psl26OrdersOK psl26Levels = true ∧
      psl26D.size = 26 ∧ eqA 26 psl26D[0]! (idA 26) = true ∧ psl26DClosed psl26X = true ∧
      psl26DClosed psl26S = true ∧ psl26DClosed (invCand 26 psl26X) = true ∧
      psl26DClosed (invCand 26 psl26S) = true ∧ (psl26D.all fun e => !eqA 26 e psl26T) = true ∧
      psl26RelOK = true ∧
      (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 0).pts.size = 26 ∧
      (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 1).pts.size = 25 ∧
      (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 2).pts.size = 12 := KernelPSL26.facts7044

end Certificates

end

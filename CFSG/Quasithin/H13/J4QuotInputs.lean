module

public import CFSG.Quasithin.H13.J4Words
public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.H13.J4Data
public meta import Certificates.Data.CFSGNative.H13.J4Data
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public meta import CFSG.Quasithin.H13.J4Defs
import Certificates.Data.CFSGNative.H13.J4Elems
public meta import CFSG.Sporadic.J4.ParSpec

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native Matrix

@[expose] def quotChecks : Bool :=
  let T := addRows (tOf (uvPairsOf basePairs)).1 idRows
  let Et := transposeRows eCols
  rowsZero (mulRows phiRows T) && rowsZero (mulRows T Et) &&
    rowsAgree (mulRows phiRows Et) 112 (fun i j => decide (i < 12) && i == j) &&
    eqRows (addRows (addRows (mulRows T gRows) (mulRows hRows T)) (mulRows Et phiRows)) idRows

@[expose] def imageChecks : Bool :=
  let uv := uvPairsOf basePairs
  let Et := transposeRows eCols
  rowsAgree (mulRows (mulRows phiRows (tOf uv).1) Et) 12 (fun a b => a == b) &&
    (List.range 12).all (fun i => rowsAgree
      (mulRows (mulRows phiRows (rConjOf uv (coreBasisConjugators.getD i [])).1) Et) 12
      (fun a b => a == b)) &&
    rowsAgree (mulRows (mulRows phiRows (uv[0]?.getD prOne).1) Et) 12
      (fun a b => (uRows12.getD a 0).testBit b) &&
    rowsAgree (mulRows (mulRows phiRows (uv[1]?.getD prOne).1) Et) 12
      (fun a b => (vRows12.getD a 0).testBit b)

end CFSG.Quasithin.H13.J4

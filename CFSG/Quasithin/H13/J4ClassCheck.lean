
module

public import CFSG.Quasithin.H13.J4ClassCheckBase

public import Certificates.Data.CFSGNative.H13.J4Class
public meta import Certificates.Data.CFSGNative.H13.J4Class
public import Certificates.Data.CFSGNative.H13.J4Elems
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Sporadic.Schreier.J4SNative
public meta import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SKCent
public meta import CFSG.Sporadic.Schreier.J4SKCent
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Quasithin.H13.J4ClassCheckInputs
public import Certificates.Certificate7034

public section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4Schreier (Pair mulP invP powP oneP wordP An Bn Xn Yn Zn etaP O xColumns
  yColumns xInvColumns yInvColumns powCols wordCols app11)
open CFSG.Quasithin.H13.J4.Native (imCols colsBounded)

theorem fusionChecks_eq : fusionChecks = true :=
  Certificates.certificate7034.1

theorem letters_uv :
    lettersOK Native.uLetters = true ∧ lettersOK Native.vLetters = true :=
  Certificates.certificate7034.2.1

theorem cls2_ok : ClsFacts xyPairs m2Cols 11385 :=
  Certificates.certificate7034.2.2.1

theorem cls3_ok : ClsFacts xyPairs xColumns 31878 :=
  Certificates.certificate7034.2.2.2.1

theorem im2_ok :
    imOK m2Cols (imCols m2Cols) = true ∧ (imCols m2Cols).length = 16 :=
  Certificates.certificate7034.2.2.2.2.1

theorem im3_ok :
    imOK xColumns (imCols xColumns) = true ∧ (imCols xColumns).length = 32 :=
  Certificates.certificate7034.2.2.2.2.2.1

theorem ker3_ok :
    app11 xColumns 1096 = 1096 ∧ 1096 ∉ imCols xColumns ∧
    ∀ a < 2048, app11 xColumns a = a → a ∈ imCols xColumns ∨ (a ^^^ 1096) ∈ imCols xColumns :=
  Certificates.certificate7034.2.2.2.2.2.2.1

theorem bounded_xy :
    colsBounded xColumns = true ∧ colsBounded xInvColumns = true ∧
    colsBounded yColumns = true ∧ colsBounded yInvColumns = true ∧ colsBounded m2Cols = true :=
  Certificates.certificate7034.2.2.2.2.2.2.2

end CFSG.Quasithin.H13.J4

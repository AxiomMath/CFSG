
module

public import Certificates.Certificate7034Base

public import CFSG.Quasithin.H13.J4ClassCheckInputs
import Certificates.Kernel.H13J4.Fusion
import Certificates.Kernel.H13J4.Cls
import Certificates.Kernel.H13J4.Small

public section

namespace Certificates

open CertificateChecks.KernelH13

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 in
open CFSG.Sporadic.J4Schreier (Pair mulP invP powP oneP wordP An Bn Xn Yn Zn etaP O xColumns
  yColumns xInvColumns yInvColumns powCols wordCols app11) in
open CFSG.Quasithin.H13.J4.Native (imCols colsBounded) in
theorem certificate7034 :
    (fusionChecks = true)
    ∧ (lettersOK Native.uLetters = true ∧ lettersOK Native.vLetters = true)
    ∧ ClsFacts xyPairs m2Cols 11385
    ∧ ClsFacts xyPairs xColumns 31878
    ∧ (imOK m2Cols (imCols m2Cols) = true ∧ (imCols m2Cols).length = 16)
    ∧ (imOK xColumns (imCols xColumns) = true ∧ (imCols xColumns).length = 32)
    ∧ (app11 xColumns 1096 = 1096 ∧ 1096 ∉ imCols xColumns ∧
       ∀ a < 2048, app11 xColumns a = a → a ∈ imCols xColumns ∨ (a ^^^ 1096) ∈ imCols xColumns)
    ∧ (colsBounded xColumns = true ∧ colsBounded xInvColumns = true ∧
       colsBounded yColumns = true ∧ colsBounded yInvColumns = true ∧ colsBounded m2Cols = true) :=
  ⟨J4Fusion.fusionChecks_true, J4Fusion.letters_ok, J4Cls.cls2_facts, J4Cls.cls3_facts,
    J4Small.im2, J4Small.im3, J4Small.ker3, J4Small.bounded⟩

end Certificates

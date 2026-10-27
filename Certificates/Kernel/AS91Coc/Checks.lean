module

public import Certificates.Data.Kernel.AS91Coc
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KS.AS91Coc

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
open CFSG.Quasithin.H13.AS91.M24G

theorem letA : letOK cocArrA PA = true := by quickRfl

theorem letAi : letOK cocArrAi PAi = true := by quickRfl

theorem letB : letOK cocArrB PB = true := by quickRfl

theorem letBi : letOK cocArrBi PBi = true := by quickRfl

theorem invA : InvPairOK 24 cocArrA cocArrAi = true := by quickRfl

theorem invB : InvPairOK 24 cocArrB cocArrBi = true := by quickRfl

theorem relOK : relOKK = true := by quickRfl

theorem maOK : (matOf 11 (fun x => (foldK x 0 cocAFive).2) == cocMA) = true := by quickRfl

theorem mw0 : mwChunk 0 = true := by quickRfl

theorem mw1 : mwChunk 1 = true := by quickRfl

theorem mw2 : mwChunk 2 = true := by quickRfl

theorem mw3 : mwChunk 3 = true := by quickRfl

theorem mw4 : mwChunk 4 = true := by quickRfl

theorem walkA : cocWalk cocGA cocTabA.toList 0 = true := by quickRfl

theorem walkB : cocWalk cocGB cocTabB.toList 0 = true := by quickRfl

end CFSG.KS.AS91Coc

end

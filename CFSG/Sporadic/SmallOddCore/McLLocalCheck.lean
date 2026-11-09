module

public import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
public import CFSG.Sporadic.SmallOddCore.SylowSimple
public import Certificates.Certificate2287

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native

theorem mclX_basic :
    mclFix.length = 35 ∧ mclXGens.size = 2 ∧ invsOK 35 mclXGens mclXInvs = true ∧
      mclXOrbits.size = 14 ∧ permOK 275 (mclCentTbl 4) = true ∧
      ∀ k < 2, permOK 275 (mclCentTbl (k + 5)) = true :=
  Certificates.certificate2287.1

theorem mclX_enum : enumOK 35 mclXGens mclXEnum = true ∧ mclXEnum.tabs.size = 20160 :=
  Certificates.certificate2287.2.1

theorem mclX_sylow : ∀ i < 4, (∀ w ∈ mclSylWords.getD i [], ∀ j ∈ w, j < mclXGens.size) ∧
    enumOK 35 (mclSylGens i) (mclSylEnum i) = true ∧
    (mclSylEnum i).tabs.size = mclSylSizes.getD i 0 ∧
    ∀ q < (mclSylEnum i).tabs.size, (mclSylEnum i).tabs[q]! = idTab 35 ∨
      wordTabS 35 #[(mclSylEnum i).tabs[q]!] (List.replicate (mclSylPrimes.getD i 0) 0) ≠
        idTab 35 ∨
      ∃ cs W, nclWordsOK 35 mclXGens mclXInvs (mclSylEnum i).tabs[q]! cs W = true :=
  Certificates.certificate2287.2.2

end CFSG.Sporadic.SmallOddCore

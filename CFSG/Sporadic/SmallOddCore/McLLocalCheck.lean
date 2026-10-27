module

public import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
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

theorem mclX_orbits :
    (∀ l < 14, orbitOK 35 mclXGens mclXInvs (wordTabS 35 mclXGens (mclXWords.getD l []))
        mclXOrbits[l]! = true ∧ mclXOrbits[l]!.tabs.size = mclXSizes.getD l 0) ∧
      (∀ l < 14, ∀ l' < 14, l ≠ l' →
        notInOK mclXOrbits[l]!.tabs (wordTabS 35 mclXGens (mclXWords.getD l' [])) = true) ∧
      (∀ l < 14, ∀ j ∈ mclXWords.getD l [], j < mclXGens.size) ∧
      wordTabS 35 mclXGens (mclXWords.getD 0 []) = idTab 35 :=
  Certificates.certificate2287.2.2.1

theorem mclX_cover : coverAllOK mclXEnum.tabs mclXOrbits = true :=
  Certificates.certificate2287.2.2.2.1

theorem mclX_sums : ∀ U : Finset (Fin 14), 0 ∈ U → (∑ l ∈ U, mclXSizes.getD l 0) ∣ 20160 →
    U = {0} ∨ U = Finset.univ :=
  Certificates.certificate2287.2.2.2.2

end CFSG.Sporadic.SmallOddCore

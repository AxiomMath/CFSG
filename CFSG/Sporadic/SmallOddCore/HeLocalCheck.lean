module

public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.Sporadic.SmallOddCore.HeLocalCheckInputs
public import Certificates.Certificate2275

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem he_local_basic :
    incListOK 8330 105 heOmega0 = true ∧
      (∀ j < 9, permChk 105 heKGens[j]! = true ∧ heKGens[j]!.size = 105 ∧
        agreeOK 105 (heInnerC0 j) heOmega0 heKGens[j]! = true) ∧
      (∀ j < 5, ∀ i ∈ heDWords.getD j [], i < 9) :=
  Certificates.certificate2275.1

theorem he_local_K : enumOK 105 heKGens heKEnum = true ∧ heKEnum.tabs.size = 40320 :=
  Certificates.certificate2275.2.1

theorem he_local_D :
    enumOK 105 heDGens heDEnum = true ∧ heDEnum.tabs.size = 20160 ∧
      normalOK 105 heDEnum.tabs heKGens heKInvs heDGens = true :=
  Certificates.certificate2275.2.2.1

theorem he_local_classes :
    heDOrbits.size = 10 ∧ heDGens.size = 5 ∧
      (∀ l < 10, orbitOK 105 heDGens heDInvs (wordTabS 105 heDGens (heDClassWords.getD l []))
        heDOrbits[l]! = true ∧ heDOrbits[l]!.tabs.size = heDClassSizes.getD l 0) ∧
      (∀ l < 10, ∀ l' < 10, l ≠ l' →
        notInOK heDOrbits[l]!.tabs (wordTabS 105 heDGens (heDClassWords.getD l' [])) = true) ∧
      (∀ l < 10, ∀ j ∈ heDClassWords.getD l [], j < heDGens.size) ∧
      wordTabS 105 heDGens (heDClassWords.getD 0 []) = idTab 105 :=
  Certificates.certificate2275.2.2.2.1

theorem he_local_cover : coverAllOK heDEnum.tabs heDOrbits = true :=
  Certificates.certificate2275.2.2.2.2.1

theorem he_local_sums : ∀ U : Finset (Fin 10), 0 ∈ U →
    (∑ l ∈ U, heDClassSizes.getD l 0) ∣ 20160 → U = {0} ∨ U = Finset.univ :=
  Certificates.certificate2275.2.2.2.2.2

end CFSG.Sporadic.SmallOddCore

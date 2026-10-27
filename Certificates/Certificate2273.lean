module

public import CFSG.Sporadic.SmallOddCore.HSLocalCheckInputs
public import CFSG.Sporadic.SmallOddCore.HSCosetInputs
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import Certificates.Kernel.Sporadic.HS.L2273F

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.PSL3Four.Native in
open CFSG.Sporadic.SmallOddCore.Native in
theorem certificate2273 : ((∀ k < 2, permOK 3850 (hsCentTbl (k + 6)) = true ∧
        (natArr (hsCentTbl (k + 6))).size = 3850) ∧
      (∀ k < 4, permOK 3850 (hsCentTbl (k + 13)) = true ∧
        (natArr (hsCentTbl (k + 13))).size = 3850) ∧
      (∀ j < 6, ∀ i ∈ hsQWords.getD j [], i < 2) ∧ (∀ j < 2, ∀ i ∈ hsDWords.getD j [], i < 4)
    )
    ∧ (CFSG.PSL3Four.Native.enumOK 3850 hsQGens hsQEnum = true ∧ hsQEnum.tabs.size = 64 ∧
      normalOK 3850 hsQEnum.tabs hsC1Tabs hsC1Invs hsQGens = true
    )
    ∧ (CFSG.PSL3Four.Native.enumOK 3850 hsC1Tabs hsC1Enum = true ∧ hsC1Enum.tabs.size = 7680 ∧
      (hsC1Enum.tabs.toList.filter (CFSG.Sporadic.SmallOddCore.commAll 3850 hsQGens)).length = 4
    )
    ∧ (CFSG.PSL3Four.Native.enumOK 3850 hsDGens hsDEnum = true ∧ hsDEnum.tabs.size = 360 ∧
      normalOK 3850 hsDEnum.tabs hsC2Tabs hsC2Invs hsDGens = true
    )
    ∧ ((∀ i < 8, ∀ j ∈ hsCosWords.getD i [], j < 4) ∧ CFSG.PSL3Four.Native.invsOK 3850 hsCosTabs hsCosInvs = true ∧
      (∀ i < 8, ∀ j < 8, i ≠ j →
        notInOK hsDEnum.tabs (comp 3850 hsCosInvs[i]! hsCosTabs[j]!) = true) ∧
      CFSG.Sporadic.SmallOddCore.commAll 3850 hsDGens hsCosTabs[1]! = true ∧
      (∀ i < 6, notInOK hsDOrbits[hsCosCls.getD i 0]!.tabs
        (conjTab 3850 hsCosInvs[i + 2]! hsCosTabs[i + 2]!
          (wordTabS 3850 hsDGens (hsDClassWords.getD (hsCosCls.getD i 0) []))) = true)
    )
    ∧ (hsDOrbits.size = 7 ∧ hsDGens.size = 2 ∧
      (∀ l < 7, orbitOK 3850 hsDGens hsDInvs (wordTabS 3850 hsDGens (hsDClassWords.getD l []))
        hsDOrbits[l]! = true ∧ hsDOrbits[l]!.tabs.size = hsDClassSizes.getD l 0) ∧
      (∀ l < 7, ∀ l' < 7, l ≠ l' →
        notInOK hsDOrbits[l]!.tabs (wordTabS 3850 hsDGens (hsDClassWords.getD l' [])) = true) ∧
      (∀ l < 7, ∀ j ∈ hsDClassWords.getD l [], j < hsDGens.size) ∧
      wordTabS 3850 hsDGens (hsDClassWords.getD 0 []) = idTab 3850
    )
    ∧ (coverAllOK hsDEnum.tabs hsDOrbits = true)
    ∧ (∀ U : Finset (Fin 7), 0 ∈ U → (∑ l ∈ U, hsDClassSizes.getD l 0) ∣ 360 →
      U = {0} ∨ U = Finset.univ
    ) := CFSG.KD.HSL.facts2273

end Certificates


module

public import CFSG.YGroups.Y443.Native.PairRelDBase

public import CFSG.YGroups.Y443.Native.Words
public import CFSG.YGroups.Y443.Native.PairRelDInputs
public import Certificates.Certificate10119
public meta import CFSG.YGroups.Y443.Native.Words
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import Certificates.Certificate10119Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native

theorem pairD_words : ∀ w ∈ pairDWords, wordLin w = 1 :=
  Certificates.certificate10119

theorem pairD_rel
    {k l : ℕ} (hk : k ∈ [5, 6, 7, 8, 9]) (hkl : k < l) (hl : l < 11) :
    (M k * M l ^ (ordI l - 1)) ^ mI k l = 1 := by
  have h := pairD_words (pairWord k l) (mem_pairWords hk hkl hl)
  rw [pairWord, wordLin_powL, wordLin_append, wordLin_powL] at h
  exact h

end CFSG.YGroups.Y443

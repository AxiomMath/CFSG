
module

public import CFSG.YGroups.Y443.Native.PairRelCBase

public import CFSG.YGroups.Y443.Native.Words
public import CFSG.YGroups.Y443.Native.PairRelCInputs
public import Certificates.Certificate10118
public meta import CFSG.YGroups.Y443.Native.Words
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import Certificates.Certificate10118Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native

theorem pairC_words : ∀ w ∈ pairCWords, wordLin w = 1 :=
  Certificates.certificate10118

theorem pairC_rel
    {k l : ℕ} (hk : k ∈ [3, 4]) (hkl : k < l) (hl : l < 11) :
    (M k * M l ^ (ordI l - 1)) ^ mI k l = 1 := by
  have h := pairC_words (pairWord k l) (mem_pairWords hk hkl hl)
  rw [pairWord, wordLin_powL, wordLin_append, wordLin_powL] at h
  exact h

end CFSG.YGroups.Y443

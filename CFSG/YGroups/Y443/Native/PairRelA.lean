
module

public import CFSG.YGroups.Y443.Native.PairRelABase

public import CFSG.YGroups.Y443.Native.Words
public import CFSG.YGroups.Y443.Native.PairRelAInputs
public import Certificates.Certificate10116
public meta import CFSG.YGroups.Y443.Native.Words
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import Certificates.Certificate10116Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native

theorem pairA_words : ∀ w ∈ pairAWords, wordLin w = 1 :=
  Certificates.certificate10116

theorem pairA_rel
    {k l : ℕ} (hk : k ∈ [0, 1]) (hkl : k < l) (hl : l < 11) :
    (M k * M l ^ (ordI l - 1)) ^ mI k l = 1 := by
  have h := pairA_words (pairWord k l) (mem_pairWords hk hkl hl)
  rw [pairWord, wordLin_powL, wordLin_append, wordLin_powL] at h
  exact h

end CFSG.YGroups.Y443

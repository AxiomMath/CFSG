
module

public import CFSG.YGroups.Y443.Native.SpiderRelBase

public import CFSG.YGroups.Y443.Native.Words
public import Certificates.Certificate10123
public meta import CFSG.YGroups.Y443.Native.Words
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import Certificates.Certificate10123Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native

theorem spider_word : wordLin spiderWord = 1 :=
  Certificates.certificate10123

theorem spider_rel :
    ((spiderFactors.map wordLin).prod) ^ 5 = 1 := by
  have h := spider_word
  rw [spiderWord, wordLin_powL, wordLin_flatten_reverse] at h
  exact h

end CFSG.YGroups.Y443

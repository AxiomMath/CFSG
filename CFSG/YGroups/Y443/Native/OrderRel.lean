
module

public import CFSG.YGroups.Y443.Native.OrderRelBase

public import CFSG.YGroups.Y443.Native.Words
public import CFSG.YGroups.Y443.Native.OrderRelInputs
public import Certificates.Certificate10115
public meta import CFSG.YGroups.Y443.Native.Words
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import Certificates.Certificate10115Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native

theorem order_words : ∀ w ∈ orderWords, wordLin w = 1 :=
  Certificates.certificate10115

theorem M_pow_ord
    {k : ℕ} (hk : k < 11) : M k ^ ordI k = 1 := by
  have h := order_words (orderWord k) (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  rw [orderWord, wordLin_powL] at h
  exact h

end CFSG.YGroups.Y443

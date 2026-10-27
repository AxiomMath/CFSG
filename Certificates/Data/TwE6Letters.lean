module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6Bits
public import Certificates.Data.E6F4Letters

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree.TwClose

open CFSG.LieType.SeitzGeneration.ExcHighThree.E6Bits CFSG.LieType.SeitzGeneration.ExcHighThree.TwBits
  CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two

@[expose] def xw1 (i : Fin 6) : Bits2 :=
  ⟨pack (xwA i), pack (xwB i)⟩

@[expose] def xw2 (i : Fin 6) : Bits2 :=
  ⟨pack (xwA2 i), pack (xwB i)⟩

@[expose] def letterBits2 (c : ℕ) : Bits2 :=
  if c < 8 then ⟨codeBits6 (f4ToE6Letter c), 0⟩
  else if c = 8 then Bits2.mul (xw1 0) (xw2 5)
  else Bits2.mul (xw1 2) (xw2 4)

end CFSG.LieType.SeitzGeneration.ExcHighThree.TwClose

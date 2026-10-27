module

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint.NativeSporadic

@[expose] def nativeModeOneEntries (s : String) : List ℕ :=
  (((s.toList.dropWhile (· != '\n')).drop 1).filter fun c => !asciiWhitespace c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

end CFSG.Quasithin

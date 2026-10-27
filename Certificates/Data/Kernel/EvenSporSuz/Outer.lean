module

public import Certificates.Data.Kernel.EvenSporSuz.Cover

public section

namespace CFSG.KC.EvenSporSuz

@[expose] def intTokK (p : List Char) : Bool :=
  digitsK p || (p.head? == some '-' && digitsK p.tail)

@[expose] def intValK (p : List Char) : ℤ :=
  if p.head? == some '-' then -(CFSG.KC.Str.decVal p.tail : ℤ) else (CFSG.KC.Str.decVal p : ℤ)

@[expose] def owOK (L : List Char) : Bool := (L.splitOn ' ').all fun p => p.isEmpty || intTokK p

@[expose] def owK (L : List Char) : List ℤ :=
  ((L.splitOn ' ').filter fun p => !p.isEmpty).map intValK

end CFSG.KC.EvenSporSuz

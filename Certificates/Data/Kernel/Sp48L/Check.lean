module

public import Certificates.Data.ONanSp48Local

public section

namespace CFSG.KC.Sp48L

open CFSG.AGLEmbedding.KFactProofs.Sp48

@[expose] def ceqP (p q : Pc) : Bool := p.m.toList == q.m.toList && p.j == q.j

@[expose] def homK : Bool := (List.range 9).all fun a => (List.range 9).all fun b =>
  !(ceqP (powP t1c a) (powP t2c b)) || a == 0

end CFSG.KC.Sp48L

module

public import CFSG.Quasithin.Vol2.Ch11SecBK10M
public import CFSG.Quasithin.Vol2.Ch11SecBK10V

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10

theorem factCCompTorus_holds :
    FactCCompTorus :=
  factCCompTorus_of_dispatch fun X _ _ hX => torusRigid_or_rank X hX

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD

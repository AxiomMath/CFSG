module

public import CFSG.Quasithin.Vol2.Ch3E213MOS12
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Over

public section

namespace CFSG.Quasithin.Ch3E213M


theorem pkgOddSingle : PkgOddSingle :=
  OS.pkgOddSingle_of GH74.GLS.IVK.ivk_1_2_general GH74.GLS.IVK.ivk_1_3a GH74.GLS.IVK.ivk_1_3b
    (by
      intro _ _ _ hF h11 _ _ _ e _ hu
      exact GH74.GLS.IVK.Proofs2.isCoatom_centralizer_of_inner hF h11 e hu)

end CFSG.Quasithin.Ch3E213M

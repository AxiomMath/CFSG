module

public import CFSG.Quasithin.Vol2.Ch3E215MDefs
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Over
public import CFSG.Quasithin.Vol2.Ch3E213MOS12

public section

namespace CFSG.Quasithin.Ch3E215M

open Ch3E213M

theorem pkgOddSingle215 : PkgOddSingle215 := by
  intro G _ _ H T M V K hS hC2 p e hp hp3 he _ hpsl hMK hAut
  refine (OS.false_of_oddSingle GH74.GLS.IVK.ivk_1_2_general GH74.GLS.IVK.ivk_1_3a
    GH74.GLS.IVK.ivk_1_3b ?_ hS hC2 hp hp3 he hpsl hMK hAut).elim
  intro _ _ _ hF h11 _ _ _ e _ hu
  exact GH74.GLS.IVK.Proofs2.isCoatom_centralizer_of_inner hF h11 e hu

end CFSG.Quasithin.Ch3E215M

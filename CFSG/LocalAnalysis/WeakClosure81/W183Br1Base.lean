module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Fam
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Weak
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Zs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem br1Base (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M}) :
    Br1Base (M.img H) (packFamilyU D V H i M) (packSpaceU D V₀ V H i M) (M.img D.T)
      (packGensU D V H i M) (packZsU D H M) x.mB i (packDeltaU D V H i M) where
  hmi := x.br1_hmi
  h131 := x.br1_h131 M
  vfix := x.br1_vfix M
  delta_le := x.br1_delta_le M
  comm_le := x.br1_comm_le M
  sylow := x.br1_sylow M
  gens := x.br1_gens M
  weakClosure := x.br1_weakClosure M hN
  zs_eq := x.br1_zs_eq M
  zs_gen := x.br1_zs_gen M
  zs_nofix := x.br1_zs_nofix M

theorem br2Common (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M}) :
    Br2Common (M.img H) (packFamilyU D V H i M) (packSpaceU D V₀ V H i M) (M.img D.T)
      (packGensU D V H i M) (packZsU D H M) x.mB i (packDeltaU D V H i M) where
  toBr1Base := x.br1Base M hN
  noOffender := x.br1_noOffender M

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end

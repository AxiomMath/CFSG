module

public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Background.FixVTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

theorem s16h_commSub_conj (L : Subgroup (MulAut W)) (σ : MulAut W) :
    commSub ⊤ (L.map (MulAut.conj σ).toMonoidHom) = (commSub ⊤ L).map σ.toMonoidHom := by
  rw [← commV_eq_commSub (L.map (MulAut.conj σ).toMonoidHom),
    CFSG.Quasithin.Vol2.Ch10.SecA.commV_map_conj, commV_eq_commSub]

theorem s16h_commSub_fixV_conj (L : Subgroup (MulAut W)) (σ : MulAut W) :
    commSub ⊤ (L.map (MulAut.conj σ).toMonoidHom) ⊓
        fixV (L.map (MulAut.conj σ).toMonoidHom) =
      (commSub ⊤ L ⊓ fixV L).map σ.toMonoidHom := by
  rw [s16h_commSub_conj L σ, fixV_map_conj_eq L σ,
    Subgroup.map_inf_eq (commSub ⊤ L) (fixV L) σ.toMonoidHom σ.injective]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexLoc
public import Certificates.Certificate4235

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex

universe u

theorem hexGeometry {X : Type u} [Group X] [MulAction X HexVtx]
    [GraphAction X hexGraph] {g : ℕ → X} (hg : ∀ j < 8, ActsAs (g j) permArrs[j]!) :
    HexGeometry X g :=
  hexGeometry_of_check hg Certificates.certificate4235

theorem hexLay0 (x : Fin 819) :
    hexGraph.dist (Sum.inl 0) (Sum.inl x) = lay0[(x : ℕ)]! :=
  hexLay0_dist Certificates.certificate4235 x

end CFSG.Quasithin.D4Hex

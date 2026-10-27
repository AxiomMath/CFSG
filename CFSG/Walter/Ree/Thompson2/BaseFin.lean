module

public import CFSG.Walter.Ree.Thompson2.BaseFin.Iso
public import CFSG.Walter.Ree.Thompson2.BaseFin.Nine
public import CFSG.Walter.Ree.Thompson2.BaseFin.Tuple

public section

namespace CFSG.Walter.Ree.T2.BaseFin

theorem pglK_pglY_cube :
    pglK * pglY ^ 3 * pglK = (pglT * pglY ^ 2) * pglK * (pglY ^ 2 * pglT⁻¹) := by
  decide

theorem k_y_cube :
    PGammaL28.k * PGammaL28.y ^ 3 * PGammaL28.k =
      (PGammaL28.t * PGammaL28.y ^ 2) * PGammaL28.k * (PGammaL28.y ^ 2 * PGammaL28.t⁻¹) :=
  Subtype.ext pglK_pglY_cube

end CFSG.Walter.Ree.T2.BaseFin

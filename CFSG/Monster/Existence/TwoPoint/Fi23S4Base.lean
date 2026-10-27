
module

public import CFSG.Monster.Existence.TwoPoint.Fi23Base
public import CFSG.Monster.Existence.TwoPoint.Fi23S4Check

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess

@[expose] noncomputable def gammaZero : MGriess := fiMkW s4WGamma

theorem fiE_eight_mul_gammaZero_eq : fiE 8 * gammaZero = fiMkW s4WE8Gamma :=
  (fiMkW_append s4WGamma fiWU[8]!).symm

theorem fiAlpha_mul_gammaZero_eq : fiAlpha * gammaZero = fiMkW s4WAlphaGamma :=
  (fiMkW_append s4WGamma fiWAlpha).symm

end CFSG.Monster.Existence

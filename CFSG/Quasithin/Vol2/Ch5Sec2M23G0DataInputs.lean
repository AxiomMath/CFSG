module

public import CFSG.Quasithin.Recognition.M22UniqueData
public meta import CFSG.Quasithin.Recognition.M22UniqueData

public section

namespace CFSG.Quasithin.H13

open CFSG.ComponentClassification.WittDesign CFSG.Sporadic.Mathieu CFSG.Quasithin.Asc94

@[expose] def m22Bt3 : M22 := m22b * m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22a * m22b⁻¹ *
  m22a * m22b * m22a * m22b * m22b * m22a * m22b * m22a * m22b⁻¹

@[expose] def m22Inv1 : M22 := m22b * m22b * m22a * m22b * m22a * m22b * m22b * m22a * m22b *
  m22a * m22b * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b * m22b * m22a * m22b⁻¹ * m22a * m22b *
  m22b

end CFSG.Quasithin.H13

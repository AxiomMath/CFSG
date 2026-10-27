module

public import CFSG.Quasithin.Recognition.M22UniqueSystem

public section

namespace CFSG.Quasithin.HSType

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

@[expose] def FactM22SubgroupIndex : Prop :=
  ∀ W : Subgroup M22, W.index < 176 →
    W = ⊤ ∨ (∃ g : M22, W = (stabilizer M22 (0 : Fin 22)).map (MulAut.conj g).toMonoidHom) ∨
      ∃ g : M22, W = m22HexStab.map (MulAut.conj g).toMonoidHom

end CFSG.Quasithin.HSType

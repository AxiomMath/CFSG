module

public import CFSG.Quasithin.Background.HSL3Rep

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L829NK

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.Quasithin.H.SL3Rep

abbrev VS : Type := Fin 3 → ZMod 2

abbrev GS : Type := VS ≃ₗ[ZMod 2] VS

@[expose] def ttSL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨1 + Matrix.single 0 2 1, by decide⟩

@[expose] noncomputable def ttGS : GS := iota ttSL

end CFSG.Quasithin.H13.L829NK

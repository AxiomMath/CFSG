module

public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CenterCheckFast

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

theorem dim_F4 : dim Tag.F4 = 52 :=
  rfl

def f4GenY (g : ℕ) : Bool :=
  g % 2 == 1

def f4GenI (g : ℕ) : Fin Tag.F4.rank :=
  ⟨g / 2 % 4, Nat.mod_lt _ (by decide)⟩

variable (L : Type) [Field L]

def f4Gen (g : ℕ) : Module.End L (RootModule Tag.F4 L) :=
  if f4GenY g then yOp Tag.F4 L (f4GenI g) 1 else xOp Tag.F4 L (f4GenI g) 1

def f4NilColActual (g q : ℕ) : List (ℕ × ℤ) :=
  (List.range 3).flatMap fun k => coeffVec .F4 (f4GenY g) (f4GenI g) (k + 1) [(q, 1)]

end CFSG.StandardType.F4ExplicitPos.CenterCheckFast
end

end

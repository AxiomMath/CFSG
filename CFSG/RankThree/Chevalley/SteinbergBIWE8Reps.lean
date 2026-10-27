module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8Code

public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.WE8.Native

@[expose] def vecOf (l : List ℤ) : L8 := fun k => l.getD k 0

@[expose] def frame (i : ℕ) : List L8 := (frameData.getD i []).map vecOf

@[expose] def rep (i : ℕ) : W8 := ((frame i).map rootReflection).prod

@[expose] def y0WordF : List (Fin Tag.E8.rank) :=
  y0Word.map fun j => ⟨j % 8, Nat.mod_lt _ (by decide)⟩

@[expose] def y0 : W8 := (coxeterSystem .E8).wordProd y0WordF

end CFSG.RankThree.Chevalley.WeylE8

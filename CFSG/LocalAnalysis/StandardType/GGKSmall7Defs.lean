module

public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6AllDefs
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGKSmall7D6Data {G : Type} [Group G] [Finite G] (Bs L K : Subgroup G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (ι : Additive ↥Bs ≃+ V)
    (φD φE : Fin 6 → MulAut ↥Bs) (hD hE : Fin 6 → V)
    (aD aE : Fin 6 → Module.Dual (ZMod 3) V),
    (∀ i w, ggLin (p := 3) ι (φD i) w = w - aD i w • hD i) ∧
    (∀ i w, ggLin (p := 3) ι (φE i) w = w - aE i w • hE i) ∧
    (∀ i, GGIsReflection 3 (φD i)) ∧ (∀ i, GGIsReflection 3 (φE i)) ∧
    (∀ i j, aD i (hD j) = (CartanMatrix.D 6 i j : ZMod 3)) ∧
    (∀ i j, aE i (hE j) = (CartanMatrix.E₆ i j : ZMod 3)) ∧
    ggAutomizer L Bs = Subgroup.closure (Set.range φD) ∧
    ggAutomizer K Bs = Subgroup.closure (Set.range φE) ∧
    Nat.card ↥(ggAutomizer L Bs) = 23040

end CFSG.StandardType

end

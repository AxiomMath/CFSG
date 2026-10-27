module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentData
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionMat

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

@[expose] def fM : SL5 := ⟨!![3, 4; 3, 1], by decide⟩

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

@[expose] def f12 : G := D.d fM

@[expose] def eb : Fin 4 → G := ![D.t, D.u, D.v, D.w]

@[expose] def vecE (a : Fin 4 → ZMod 2) : G :=
  D.t ^ (a 0).val * D.u ^ (a 1).val * D.v ^ (a 2).val * D.w ^ (a 3).val

@[expose] def IsBasisRep (ρ : normalizer (D.E : Set G) →* GL (Fin 4) (ZMod 2)) : Prop :=
  ∀ (g : normalizer (D.E : Set G)) (i : Fin 4),
    (g : G)⁻¹ * D.eb i * g = D.vecE fun j => (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j

end SwapData

end CFSG.OddTranspositions.PartThree.Wong

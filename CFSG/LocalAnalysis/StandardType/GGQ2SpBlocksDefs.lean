module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneRaw
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)

@[expose] def tau (u : PlaneRaw.V m) : ↥(StatedSp m K) :=
  spPlaneTorus m ζ (fun i => Multiplicative.ofAdd (u i))

@[expose] def torusSet (U : Submodule (ZMod 3) (PlaneRaw.V m)) : Set (GL (Fin m ⊕ Fin m) K) :=
  {g | ∃ u ∈ U, g = ((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K)}

@[expose] def planeIdem (S : Finset (Fin m)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  Matrix.diagonal fun x => if (Sum.elim id id x) ∈ S then 1 else 0

@[expose] def levi (S : Finset (Fin m)) : Subgroup ↥(StatedSp m K) :=
  (glFixing (1 - planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)).comap
    (StatedSp m K).subtype

@[expose] def blockGroup : PlaneRaw.Code m → Subgroup ↥(StatedSp m K)
  | .zero S => levi m S
  | .extension e => levi m (PlaneRaw.Code.extSupport e) ⊓
      Subgroup.centralizer ({tau ζ m e} : Set ↥(StatedSp m K))

@[expose] def Ycode (c : PlaneRaw.Code m) : Subgroup ↥(StatedSp m K) :=
  ⁅blockGroup ζ m c, blockGroup ζ m c⁆

end

end CFSG.StandardType.GGQ2Frame.SpBlocks

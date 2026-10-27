module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def TcC1Row {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (ΨJ Ψx : Set (Fin τ.rank → ℤ)) : Prop :=
  (compRank ΨJ = 1 ∧ ΨJ.ncard = 2 ∧ componentOrbitLength ρ ΨJ = 2 ∧
      twistKindOf ρ ΨJ = .inner ∧
      ((compRank Ψx = 2 ∧ Ψx.ncard = 6 ∧ componentOrbitLength ρ Ψx = 2 ∧
          twistKindOf ρ Ψx = .inner) ∨
       (compRank Ψx = 4 ∧ Ψx.ncard = 24 ∧ componentOrbitLength ρ Ψx = 1 ∧
          twistKindOf ρ Ψx = .twoD) ∨
       (compRank Ψx = 5 ∧ Ψx.ncard = 30 ∧ componentOrbitLength ρ Ψx = 1 ∧
          twistKindOf ρ Ψx = .inner))) ∨
  (compRank ΨJ = 2 ∧ ΨJ.ncard = 6 ∧ componentOrbitLength ρ ΨJ = 2 ∧ twistKindOf ρ ΨJ = .inner ∧
      compRank Ψx = 5 ∧ Ψx.ncard = 30 ∧ componentOrbitLength ρ Ψx = 1 ∧
      twistKindOf ρ Ψx = .inner)

@[expose] def TcC1RowNegOne {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (ΨJ Ψx : Set (Fin τ.rank → ℤ)) : Prop :=
  compRank ΨJ = 1 ∧ ΨJ.ncard = 2 ∧ componentOrbitLength ρ ΨJ = 3 ∧ twistKindOf ρ ΨJ = .inner ∧
    ((compRank Ψx = 2 ∧ Ψx.ncard = 6 ∧ componentOrbitLength ρ Ψx = 3 ∧
        twistKindOf ρ Ψx = .suN) ∨
     (compRank Ψx = 4 ∧ Ψx.ncard = 24 ∧ componentOrbitLength ρ Ψx = 1 ∧
        twistKindOf ρ Ψx = .exc) ∨
     (compRank Ψx = 5 ∧ Ψx.ncard = 30 ∧ componentOrbitLength ρ Ψx = 1 ∧
        twistKindOf ρ Ψx = .suN))

@[expose] def TcC1RowNegTwo {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (ΨJ Ψx : Set (Fin τ.rank → ℤ)) : Prop :=
  compRank ΨJ = 1 ∧ ΨJ.ncard = 2 ∧ componentOrbitLength ρ ΨJ = 2 ∧ twistKindOf ρ ΨJ = .inner ∧
    ((compRank Ψx = 2 ∧ Ψx.ncard = 6 ∧ componentOrbitLength ρ Ψx = 2 ∧
        twistKindOf ρ Ψx = .inner) ∨
     (compRank Ψx = 4 ∧ Ψx.ncard = 24 ∧ componentOrbitLength ρ Ψx = 1 ∧
        twistKindOf ρ Ψx = .twoD))

end CFSG.StandardType.TableCRes

end

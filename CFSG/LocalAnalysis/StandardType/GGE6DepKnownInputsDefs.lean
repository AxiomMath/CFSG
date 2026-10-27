module

public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelCoord

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGE6DepPerpXNotInL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGE6DepPerpCfg p Bs L K → x ∉ L

@[expose] def GGE6IsoPt (v : Fin 6 → ZMod 3) : Prop :=
  v ∈ NoOffRest.hypE6 ∧ v ≠ 0 ∧ E6Dep.norm6 (E6Dep.coordF.mulVec v) = 0

@[expose] def GGE6DepNonIsoProp (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup 3 5 R I L' ψ A → Nat.card A = 3 ^ 5 →
      ∀ (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup L') (w : Fin 6 → L'),
        GGE6ThreeWeylModelWith ψ.ker A Φ T w →
          ∀ a : A, GGE6IsoPt (Multiplicative.toAdd (Φ a)) →
            ∀ J : Subgroup L', IsComponentOf J (ggFix (a : MulAut L')) →
              ∃ J' : Subgroup L', IsComponentOf J' (ggFix (a : MulAut L')) ∧ J' ≠ J

@[expose] def GGE6DepNonIsoPt : Prop :=
  ∀ lab : LargeEvenLabel, GGE6DepLabel lab → LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGE6DepNonIsoProp R I

@[expose] def GGE6DepPerpTablePInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGE6DepPerpCfg p Bs L K →
          ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → GGE6DepPerpCfg p Bs L K'

end CFSG.StandardType

end

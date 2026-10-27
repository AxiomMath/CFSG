module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggTPJLabel (lab : LargeEvenLabel) : LargeEvenLabel :=
  if lab.tag = LargeEvenLieTag.E6 then ⟨.A, 5, lab.n⟩ else ⟨.twA, 5, lab.n⟩

@[expose] def GGTPClassicalLab (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD

@[expose] def GGTPJLayer (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup 3 5 R I L' ψ A → Nat.card A = 3 ^ 5 →
    ¬ 3 ∣ Nat.card (Subgroup.center L') →
    ∀ c : ↥A, GGCorootPt 3 (ggTorusAut A) c →
      ∀ J : Subgroup L', IsComponentOf J (ggFix (c : MulAut L')) →
        GGHasLabel (ggTPJLabel lab) (J ⧸ Subgroup.center J) ∧ ¬ 3 ∣ Nat.card (Subgroup.center J) ∧
          3 ∣ Nat.card J

@[expose] def GGTPJLayerInput : Prop :=
  ∀ lab : LargeEvenLabel, GGE6DepLabel lab → LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTPJLayer lab R I

@[expose] def GGTPJStab (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup 3 5 R I L' ψ A → Nat.card A = 3 ^ 5 →
    ¬ 3 ∣ Nat.card (Subgroup.center L') →
    ∀ c : ↥A, GGCorootPt 3 (ggTorusAut A) c →
      ∀ J : Subgroup L', IsComponentOf J (ggFix (c : MulAut L')) →
        ∀ φ ∈ ggTorusAut A, φ c = c →
          φ ∈ ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A

@[expose] def GGTPJStabInput : Prop :=
  ∀ lab : LargeEvenLabel, GGE6DepLabel lab → LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTPJStab R I

@[expose] def GGTPClassicalExcl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGE6DepPerpCfg p Bs L K →
          ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
            ∀ labJ labK : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labK →
              GGTPClassicalLab labK → GGHasLabel labJ (J ⧸ Subgroup.center J) →
                GGHasLabel labK (K' ⧸ Subgroup.center K') → GGTablePRow p labJ labK → False

end CFSG.StandardType

end

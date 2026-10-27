module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.AbsolutelyIrreducible

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2ReflAbsIrred {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs : Subgroup G) :
    Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V),
    Theory.Representation.IsAbsolutelyIrreducible
      ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod p) (M := V)).comp
        ((ggLin (p := p) ι).comp (ggReflGp p Bs).subtype) :
        Representation (ZMod p) ↥(ggReflGp p Bs) V)

@[expose] def GGQ2ReflInM {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection p φ →
    g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2Prop898 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J → ∀ [Fact p.Prime],
      GGQ2ReflAbsIrred p Bs → GGQ2ReflInM p B Bs x L D J → GGQ2P3 p Bs x

end CFSG.StandardType

end

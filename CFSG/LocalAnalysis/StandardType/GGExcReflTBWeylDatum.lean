module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourDom
public import CFSG.LocalAnalysis.StandardType.GGTBWInputDefs

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGExcReflTBWeylDatum (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Bs L J : Subgroup G) where
  Λ : Type
  [instFintype : Fintype Λ]
  coxeter : CoxeterMatrix Λ
  cartan : Matrix Λ Λ ℤ
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod p) V]
  model : Additive ↥Bs ≃+ V
  simple : Λ → MulAut ↥Bs
  coroot : Λ → V
  root : Λ → Module.Dual (ZMod p) V
  isWeyl : GGIsWeylMatrix coxeter
  isCartan : GGIntCartan coxeter cartan
  three_le_card : 3 ≤ Fintype.card Λ
  pairing : ∀ i j, root i (coroot j) = (cartan i j : ZMod p)
  simple_apply : ∀ i w, ggLin (p := p) model (simple i) w = w - root i w • coroot i
  automizer_eq : ggAutomizer L Bs = Subgroup.closure (Set.range simple)
  tbHyp : Module.finrank (ZMod p) V ≤
        Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range coroot)) + 1 ∨
      Module.finrank (ZMod p) (ggFixedSubmodule (p := p) model (ggAutNormalClosure L J Bs)) ≤ 1

attribute [instance] GGExcReflTBWeylDatum.instFintype GGExcReflTBWeylDatum.instAddCommGroup
  GGExcReflTBWeylDatum.instModule

@[expose] def GGExcReflTBWeylDatumQFourOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGInnerDiagOnLabel S p Bs L →
        ∀ [Fact p.Prime], Nonempty (GGExcReflTBWeylDatum p Bs L J)

@[expose] def GGTBJNoncommReflOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGInnerDiagOnLabel S p Bs L →
        ∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs,
          GGIsReflection p a ∧ GGIsReflection p b ∧ a * b ≠ b * a

end CFSG.StandardType

end

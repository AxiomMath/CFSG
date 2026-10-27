module

public import CFSG.LocalAnalysis.StandardType.GGQTwoModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

structure GGQ2LDatum (p : ℕ) [Fact p.Prime] {G : Type} [Group G] (Bs L : Subgroup G) (x : G) where
  Λ : Type
  [instFintype : Fintype Λ]
  [instDecEq : DecidableEq Λ]
  coxeter : CoxeterMatrix Λ
  cartan : Matrix Λ Λ ℤ
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod p) V]
  model : Additive ↥Bs ≃+ V
  hx : x ∈ Bs
  simple : Λ → MulAut ↥Bs
  coroot : Λ → V
  root : Λ → Module.Dual (ZMod p) V
  isWeyl : GGIsWeylMatrix coxeter
  isCartan : GGIntCartan coxeter cartan
  pairing : ∀ i j, root i (coroot j) = (cartan i j : ZMod p)
  simple_apply : ∀ i w, ggLin (p := p) model (simple i) w = w - root i w • coroot i
  automizer_L : ggAutomizer L Bs = Subgroup.closure (Set.range simple)
  fixed_x : ggFixedSubmodule (p := p) model (ggAutomizer L Bs) =
    Submodule.span (ZMod p) {model (Additive.ofMul ⟨x, hx⟩)}

attribute [instance] GGQ2LDatum.instFintype GGQ2LDatum.instDecEq GGQ2LDatum.instAddCommGroup
  GGQ2LDatum.instModule

@[expose] def GGQ2LDatum.xV {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) : M.V :=
  M.model (Additive.ofMul ⟨x, M.hx⟩)

@[expose] def GGQ2LDatum.coSpan {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) : Submodule (ZMod p) M.V :=
  Submodule.span (ZMod p) (Set.range M.coroot)

@[expose] def GGQ2LDatum.rootMap {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) : M.V →ₗ[ZMod p] (M.Λ → ZMod p) :=
  LinearMap.pi M.root

@[expose] def GGQ2LDatum.ShapeFull {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) : Prop :=
  x ∉ L ∧ LinearIndependent (ZMod p) M.coroot ∧ M.xV ∉ M.coSpan ∧
    M.coSpan ⊔ Submodule.span (ZMod p) {M.xV} = ⊤

@[expose] def GGQ2LDatum.ShapeA {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) : Prop :=
  x ∈ L ∧ LinearIndependent (ZMod p) M.coroot ∧ M.xV ∈ M.coSpan ∧
    Module.finrank (ZMod p) M.V = Fintype.card M.Λ + 1 ∧ Function.Surjective M.rootMap

@[expose] def GGQ2LDatum.ShapeB {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) : Prop :=
  x ∉ L ∧ Module.finrank (ZMod p) M.coSpan + 1 = Fintype.card M.Λ ∧ M.xV ∉ M.coSpan ∧
    M.coSpan ⊔ Submodule.span (ZMod p) {M.xV} = ⊤

@[expose] def GGQ2LDatum.ShapeC {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) : Prop :=
  x ∉ L ∧ Module.finrank (ZMod p) M.coSpan + 1 = Fintype.card M.Λ ∧ M.xV ∉ M.coSpan ∧
    Module.finrank (ZMod p) M.V = Fintype.card M.Λ + 1 ∧ Function.Surjective M.rootMap

@[expose] def GGQ2LDatum.ShapeD {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) : Prop :=
  x ∈ L ∧ LinearIndependent (ZMod p) M.coroot ∧ M.coSpan = ⊤

@[expose] def GGQ2LDatum.Shape {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum p Bs L x) : Prop :=
  M.ShapeFull ∨ M.ShapeA ∨ M.ShapeB ∨ M.ShapeC ∨ M.ShapeD

@[expose] def GGQ2LDatum.HeartShape {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) : Prop :=
  M.ShapeB ∨ M.ShapeD

@[expose] def GGQ2TBLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ 4 ≤ lab.rank) ∨ ((lab.tag = .B ∨ lab.tag = .C) ∧ 4 ≤ lab.rank) ∨
    (lab.tag = .D ∧ Even lab.rank ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ Odd lab.rank ∧ 4 ≤ lab.rank) ∨
    lab.tag = .F4 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8

@[expose] def GGQ2LabelWeyl (lab : LargeEvenLabel) {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  match lab.tag with
  | .twA => ∃ e : Fin lab.rank ≃ ι, M = (CoxeterMatrix.A lab.rank).reindex e
  | .B | .C => ∃ e : Fin lab.rank ≃ ι, M = (CoxeterMatrix.B lab.rank).reindex e
  | .D | .twD => ∃ e : Fin lab.rank ≃ ι, M = (ggCoxeterMatrixD lab.rank).reindex e
  | .F4 => ∃ e : Fin 4 ≃ ι, M = CoxeterMatrix.F₄.reindex e
  | .twE6 => ∃ e : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e
  | .E7 => ∃ e : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex e
  | .E8 => ∃ e : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex e
  | _ => False

@[expose] def GGQ2TableBI1Fail : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J → ∀ [Fact p.Prime],
      ∃ labL : LargeEvenLabel, GGLabQTwo p labL ∧ GGQ2TBLabel labL ∧
        LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) ∧
        ∃ M : GGQ2LDatum p Bs L x, GGQ2LabelWeyl labL M.coxeter ∧ M.Shape ∧
          (Module.finrank (ZMod p) M.V ≤ Fintype.card M.Λ →
            (labL.tag = .twA ∧ 3 ∣ labL.rank + 1) ∨ labL.tag = .twE6)

end CFSG.StandardType

end

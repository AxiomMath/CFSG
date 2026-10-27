module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

structure GGQTwoAmbModel (p : ℕ) [Fact p.Prime] {G : Type} [Group G] (Bs : Subgroup G) (x y : G)
    (L H : Subgroup G) where
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  coxeter : CoxeterMatrix ι
  cartan : Matrix ι ι ℤ
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod p) V]
  model : Additive ↥Bs ≃+ V
  hx : x ∈ Bs
  hy : y ∈ Bs
  simple : ι → MulAut ↥Bs
  coroot : ι → V
  root : ι → Module.Dual (ZMod p) V
  a : ι
  b : ι
  a_ne_b : a ≠ b
  a_leaf : ∃! c, c ≠ a ∧ cartan a c ≠ 0
  isWeyl : GGIsWeylMatrix coxeter
  isCartan : GGIntCartan coxeter cartan
  pairing : ∀ i j, root i (coroot j) = (cartan i j : ZMod p)
  simple_apply : ∀ i w, ggLin (p := p) model (simple i) w = w - root i w • coroot i
  automizer_L : ggAutomizer L Bs = Subgroup.closure (simple '' {k | k ≠ a})
  simple_a_mem : simple a ∈ ggAutomizer H Bs
  fixed_x : ggFixedSubmodule (p := p) model (ggAutomizer L Bs) =
    Submodule.span (ZMod p) {model (Additive.ofMul ⟨x, hx⟩)}
  y_fixed_J : ∀ k, k ≠ a → k ≠ b → simple k ⟨y, hy⟩ = ⟨y, hy⟩

attribute [instance] GGQTwoAmbModel.instFintype GGQTwoAmbModel.instDecEq
  GGQTwoAmbModel.instAddCommGroup GGQTwoAmbModel.instModule

@[expose] def GGQTwoAmbModel.toLin {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H) : GGQ2Lin p where
  ι := M.ι
  coxeter := M.coxeter
  cartan := M.cartan
  V := M.V
  coroot := M.coroot
  root := M.root
  a := M.a
  b := M.b
  a_ne_b := M.a_ne_b
  a_leaf := M.a_leaf
  isWeyl := M.isWeyl
  isCartan := M.isCartan
  pairing := M.pairing

@[expose] noncomputable def GGQTwoAmbModel.xV {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H) : M.V :=
  M.model (Additive.ofMul ⟨x, M.hx⟩)

@[expose] noncomputable def GGQTwoAmbModel.yV {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H) : M.V :=
  M.model (Additive.ofMul ⟨y, M.hy⟩)

end CFSG.StandardType

end

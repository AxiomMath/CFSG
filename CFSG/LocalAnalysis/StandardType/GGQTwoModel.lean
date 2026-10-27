module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

structure GGQTwoModel (p : ℕ) [Fact p.Prime] {G : Type} [Group G] (Bs : Subgroup G) (x y : G)
    (D L J K : Subgroup G) where
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
  automizer_K : ggAutomizer K Bs = Subgroup.closure (simple '' {k | k ≠ b})
  fixed_x : ggFixedSubmodule (p := p) model (ggAutomizer L Bs) =
    Submodule.span (ZMod p) {model (Additive.ofMul ⟨x, hx⟩)}
  fixed_y : ggFixedSubmodule (p := p) model (ggAutomizer K Bs) =
    Submodule.span (ZMod p) {model (Additive.ofMul ⟨y, hy⟩)}

attribute [instance] GGQTwoModel.instFintype GGQTwoModel.instDecEq GGQTwoModel.instAddCommGroup
  GGQTwoModel.instModule

@[expose] def GGQTwoBasis {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) : Prop :=
  LinearIndependent (ZMod p) M.coroot ∧ Fintype.card M.ι = Module.finrank (ZMod p) M.V

@[expose] def GGQTwoTwoNodeRowAt {G : Type} [Group G] (p : ℕ) (X J : Subgroup G) : Prop :=
  ∃ labX labJ : LargeEvenLabel, LargeEvenMarking X (fun lab _ _ _ _ _ => lab = labX) ∧
    LargeEvenMarking J (fun lab _ _ _ _ _ => lab = labJ) ∧
    ((labJ.tag = .A ∧ labX.tag = .A ∧ labX.rank = labJ.rank + 2 ∧ labX.n = labJ.n ∧
        p ∣ labJ.rank + 3 ∧ p ∣ 2 ^ labJ.n - 1) ∨
      (labJ.tag = .twA ∧ labX.tag = .twA ∧ labX.rank = labJ.rank + 2 ∧ labX.n = labJ.n ∧
        p ∣ labJ.rank + 3 ∧ p ∣ 2 ^ labJ.n + 1) ∨
      (labJ.tag = .D ∧ labJ.rank = 4 ∧ labX.tag = .E6 ∧ labX.n = labJ.n ∧ p = 3 ∧
        p ∣ 2 ^ labJ.n - 1) ∨
      (labJ.tag = .D ∧ labJ.rank = 4 ∧ labX.tag = .twE6 ∧ labX.n = labJ.n ∧ p = 3 ∧
        p ∣ 2 ^ labJ.n + 1))

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKFormDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelActs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelCoord
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameDefs

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

@[expose] def hpart (w : Vec6) : Vec6 := w - w 5 • Pi.single 5 (1 : ZMod 3)

@[expose] def GGE6DepCoord (Bs L : Subgroup G) (x : G) (hxBs : x ∈ Bs)
    (ι : Additive ↥Bs ≃+ Vec6) : Prop :=
  ι (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 5 1 ∧
    (∀ b : ↥Bs, (b : G) ∈ L ↔ ι (Additive.ofMul b) 5 = 0) ∧
    (∀ φ ∈ ggAutomizer L Bs, ∃ g ∈ closureL, ActsAs ι φ g) ∧
    (∀ g ∈ closureL, ∃ φ ∈ ggAutomizer L Bs, ActsAs ι φ g)

@[expose] def ActsAsK {Bs : Subgroup G} (κ : Additive ↥Bs →+ Vec6) (φ : MulAut ↥Bs) (g : Mat6) :
    Prop :=
  ∀ b : ↥Bs, κ (Additive.ofMul (φ b)) = g.mulVec (κ (Additive.ofMul b))

theorem ActsAsK.mul {Bs : Subgroup G} {κ : Additive ↥Bs →+ Vec6} {φ ψ : MulAut ↥Bs} {g h : Mat6}
    (hφ : ActsAsK κ φ g) (hψ : ActsAsK κ ψ h) : ActsAsK κ (φ * ψ) (g * h) := by
  intro b
  rw [MulAut.mul_apply, hφ (ψ b), hψ b, Matrix.mulVec_mulVec]

theorem ActsAsK.one {Bs : Subgroup G} (κ : Additive ↥Bs →+ Vec6) :
    ActsAsK κ (1 : MulAut ↥Bs) 1 := by
  intro b
  rw [MulAut.one_apply, Matrix.one_mulVec]

@[expose] def GGE6DepKFrame (Bs X : Subgroup G) (y : G) (κ : Additive ↥Bs →+ Vec6) : Prop :=
  (∀ b : ↥Bs, κ (Additive.ofMul b) = 0 ↔ (b : G) ∈ Subgroup.zpowers y) ∧
    (∀ b : ↥Bs, κ (Additive.ofMul b) 5 = 0) ∧
    (∀ v : Vec6, v 5 = 0 → ∃ b : ↥Bs, κ (Additive.ofMul b) = v) ∧
    (∀ φ ∈ ggAutomizer X Bs, ∃ g ∈ closureL, ActsAsK κ φ g) ∧
    (∀ g ∈ closureL, ∃ φ ∈ ggAutomizer X Bs, ActsAsK κ φ g)

@[expose] noncomputable def kappaOf {Bs X : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (Φ : ↥(ggGamma X hBsN).range →* Multiplicative (Fin 6 → ZMod 3)) :
    Additive ↥Bs →+ Vec6 where
  toFun b := coordF.mulVec
    (Multiplicative.toAdd (Φ ((ggGamma X hBsN).rangeRestrict (Additive.toMul b))))
  map_zero' := by
    simp only [toMul_zero, map_one]
    exact Matrix.mulVec_zero _
  map_add' b b' := by
    simp only [toMul_add, map_mul]
    exact Matrix.mulVec_add _ _ _

end E6Dep

end CFSG.StandardType

end

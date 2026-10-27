module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.H13.L829N

open Module

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def InvUnder (S : Subgroup (W ≃ₗ[ZMod 2] W)) (P : Submodule (ZMod 2) W) : Prop :=
  ∀ s ∈ S, ∀ w ∈ P, s w ∈ P

structure HBData (Sg : Subgroup (W ≃ₗ[ZMod 2] W)) (WB : Submodule (ZMod 2) W) : Prop where
  inv : InvUnder Sg WB
  dim_le : Module.finrank (ZMod 2) WB ≤ 5
  fix_le : ∀ P : Submodule (ZMod 2) W, P ≤ WB → (∀ s ∈ Sg, ∀ w ∈ P, s w = w) →
    Module.finrank (ZMod 2) P ≤ 1
  irr : ∀ P : Submodule (ZMod 2) W, P ≤ WB → P ≠ ⊥ → InvUnder Sg P →
    (∀ Q : Submodule (ZMod 2) W, Q ≤ P → InvUnder Sg Q → Q = ⊥ ∨ Q = P) →
    Module.finrank (ZMod 2) P = 1 ∨
      (Module.finrank (ZMod 2) P = 4 ∧ ∃ s ∈ Sg, ∃ s' ∈ Sg, ∃ w ∈ P, s (s' w) ≠ s' (s w))

structure TransvConfig (Sg Gg Tg Vg : Subgroup (W ≃ₗ[ZMod 2] W)) (WB : Submodule (ZMod 2) W) :
    Prop where
  nontrivial : Nontrivial W
  irreducible : ∀ P : Submodule (ZMod 2) W, InvUnder (Sg ⊔ Gg ⊔ Tg) P → P = ⊥ ∨ P = ⊤
  comm : ∀ g ∈ Gg, ∀ s ∈ Sg, g * s = s * g
  T_norm_S : ∀ t ∈ Tg, ∀ s ∈ Sg, t * s * t⁻¹ ∈ Sg
  T_norm_G : ∀ t ∈ Tg, ∀ g ∈ Gg, t * g * t⁻¹ ∈ Gg
  V_le : Vg ≤ Gg
  V_sq : ∀ v ∈ Vg, v * v = 1
  gen : Gg = Subgroup.closure {g | ∃ v ∈ Vg, ∃ x ∈ Gg ⊔ Tg, g = x * v * x⁻¹}
  V_ne : ∃ v ∈ Vg, v ≠ 1
  WB_T : InvUnder Tg WB
  WB_V : ∀ v ∈ Vg, ∀ w, v w - w ∈ WB
  hb : HBData Sg WB

end CFSG.Quasithin.H13.L829N

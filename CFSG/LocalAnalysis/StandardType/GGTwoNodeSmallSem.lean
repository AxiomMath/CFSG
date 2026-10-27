module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Core
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Pt.V (P : Pt) : Type := Fin P.D → ZMod P.p

@[expose] def Pt.vec (P : Pt) (v : Vec) : P.V := fun i => ((v.getD i 0 : ℕ) : ZMod P.p)

@[expose] def Pt.dot (P : Pt) (f w : P.V) : ZMod P.p := ∑ i, f i * w i

@[expose] def Pt.WF (P : Pt) : Prop := ∀ r ∈ P.gens, P.dot (P.vec r.f) (P.vec r.h) = 2

@[expose] def Pt.genSet (P : Pt) : Set (P.V ≃ₗ[ZMod P.p] P.V) :=
  {e | ∃ r ∈ P.gens, ∀ w, e w = w - P.dot (P.vec r.f) w • P.vec r.h}

@[expose] def Pt.group (P : Pt) : Subgroup (P.V ≃ₗ[ZMod P.p] P.V) := Subgroup.closure P.genSet

@[expose] def IsTransv {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (g : V ≃ₗ[ZMod p] V) : Prop :=
  Module.finrank (ZMod p) (CFSG.StandardType.ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w

@[expose] def Pt.FrameViolation (P : Pt) : Prop :=
  ∃ w : P.V, (∀ r ∈ P.gens.take P.nFrame, P.dot (P.vec r.f) w = 0) ∧
    w ∉ Submodule.span (ZMod P.p) {P.vec P.x}

end CFSG.TwoNodeSmall

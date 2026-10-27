module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {G : Type} [Group G] [Finite G]

structure GGCaseZeroData (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop where
  cfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦
  mem : x ∈ Bs
  fix : ∀ φ ∈ ggAInf p B Bs x L D J, φ ⟨x, mem⟩ = ⟨x, mem⟩
  sat : ∀ a ∈ ggAInf p B Bs x L D J, GGIsReflection p a → a ⟨x, mem⟩ = ⟨x, mem⟩ →
    (∃ g ∈ ggAInf p B Bs x L D J, ∃ r ∈ ggAutomizer L Bs, GGIsReflection p r ∧ a = g * r * g⁻¹) →
      a ∈ ggAutomizer L Bs
  frame : ∃ (ιL : Type) (_ : Fintype ιL) (ML : CoxeterMatrix ιL),
    (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) ∧ GGWeylOfType p ML (ggAutomizer L Bs)
  fixL : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x

end

section

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

variable (p) in
@[expose] def GGCZFrameD {m : ℕ} (Bs : Subgroup G) (AL : Subgroup (MulAut ↥Bs))
    (ιV : Additive ↥Bs ≃+ V) (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V) : Prop :=
  GGCZDual e φ ∧ (∀ a ∈ AL, GGIsReflection p a → ggLin (p := p) ιV a ∈ ggCZRD e φ) ∧
    (∀ r ∈ ggCZRD e φ, ∃ a ∈ AL, ggLin (p := p) ιV a = r) ∧
    ∀ a ∈ AL, ∀ v, (∀ k, φ k v = 0) → ggLin (p := p) ιV a v = v

end

end CFSG.StandardType

end

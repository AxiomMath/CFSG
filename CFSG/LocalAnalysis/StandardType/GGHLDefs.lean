module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

section HL

variable {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V] {Λ : Type*}

@[expose] def ggDiagramSet (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) :
    Set (V ≃ₗ[ZMod p] V) :=
  {g | ∃ π : Λ ≃ Λ, ∀ i, g (h i) = h (π i) ∧ ∀ v, α (π i) (g v) = α i v}

@[expose] noncomputable def ggHL (ι : Additive E ≃+ V) (φ : Λ → MulAut E) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) : Subgroup (V ≃ₗ[ZMod p] V) :=
  Subgroup.closure (Set.range (fun i => ggLin (p := p) ι (φ i)) ∪
    {LinearEquiv.neg (ZMod p)} ∪ ggDiagramSet h α)

end HL

section Concl

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}

@[expose] def GGWNormConcl (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (φ' : MulAut ↥A) : Prop :=
  (∃ c : (ZMod p)ˣ, ∃ w ∈ ggHL ι φ h α, ∀ v, ggLin (p := p) ι φ' v = (c : ZMod p) • w v) ∧
    (GGIsReflection p φ' → ggLin (p := p) ι φ' ∈ ggHL ι φ h α)

end Concl

end CFSG.StandardType

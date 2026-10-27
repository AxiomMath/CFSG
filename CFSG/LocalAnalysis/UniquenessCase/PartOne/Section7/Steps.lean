module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Config
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Layer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

@[expose] def Step74 (k : Sec7Core4 G) : Prop :=
  ∀ H : Subgroup G, Config k H → CFSG.Open.pCoreOf 2 k.M ⊓ H = ⊥

@[expose] def Step75 (k : Sec7Core4 G) : Prop :=
  ∀ H : Subgroup G, Config k H →
    ⁅layerLift k.p H, (CFSG.pPrimeCore k.p ↥H).map H.subtype⁆ = ⊥

@[expose] def Step72L (k : Sec7Core4 G) : Prop :=
  ∀ H : Subgroup G, Config k H → ¬ layerLift k.p H ≤ k.M

@[expose] def Step76C (k : Sec7Core4 G) : Prop :=
  ∀ H : Subgroup G, Config k H → ∀ x y : G, x ∈ H ⊓ k.M → y ∈ H ⊓ k.M →
    IsPGroup k.p (Subgroup.zpowers x) → x ∉ (CFSG.pPrimeCore k.p ↥H).map H.subtype →
    (orderOf y).Prime → orderOf y ≠ 2 → orderOf y ≠ k.p →
    y ∉ (CFSG.pPrimeCore k.p ↥H).map H.subtype → x * y = y * x →
    ∃ j ∈ layerLift k.p H, IsPGroup k.p (Subgroup.zpowers j) ∧
      j ∉ k.M ∧ j * y * j⁻¹ * y⁻¹ ∈ (CFSG.pPrimeCore k.p ↥H).map H.subtype

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

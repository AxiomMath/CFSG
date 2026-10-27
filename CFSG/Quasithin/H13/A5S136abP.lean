module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin

@[expose] def LieZCentList (X : Type) [Group X] : Prop :=
  ∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel X .PSL 2 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel X .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel X .PSU 3 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ SuzukiModel X 2 f)

@[expose] def FactLieZCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieZCentList X → ∀ (P : Sylow 2 X) (u w k : X),
    u ∈ (P : Subgroup X) → (∀ t ∈ (P : Subgroup X), u * t = t * u) → u ≠ 1 →
    w ∈ (P : Subgroup X) → (∀ t ∈ (P : Subgroup X), w * t = t * w) →
    Odd (orderOf k) → k * u = u * k → k * w = w * k

@[expose] def FactLieZCentPGL3 : Prop :=
  ∀ (s : Bool) (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X] [Finite X], IsPGLEps3 s (2 ^ f) X →
    ∀ (P : Sylow 2 X) (u w k : X),
    u ∈ (P : Subgroup X) → (∀ t ∈ (P : Subgroup X), u * t = t * u) → u ≠ 1 →
    w ∈ (P : Subgroup X) → (∀ t ∈ (P : Subgroup X), w * t = t * w) →
    Odd (orderOf k) → k * u = u * k → k * w = w * k

@[expose] def FactLieOutAbelian : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.QuasithinUnique.Ch1.SQTKCharTwoLie X →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 →
    ∀ α β : MulAut X, ∃ g : X, α * β * α⁻¹ * β⁻¹ = MulAut.conj g

end CFSG.Quasithin.H13.A5

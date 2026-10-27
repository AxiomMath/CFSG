module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def FactL33M11 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    (StatedClassicalModel Q .PSL 3 3 1 ∨ Nonempty (Q ≃* ↥(StatedSL 3 (ZMod 3))) ∨
      Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) →
    ∀ S Y : Subgroup Q, IsSylowTwoOf S ⊤ → Y = oTwoUpper Y →
      S ≤ Subgroup.normalizer (Y : Set Q) → (∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) →
      (pCoreOf 2 Y).relIndex Y = 9 →
      ∃ s ∈ S, ∃ y ∈ Y, s ^ 4 * y * (s ^ 4)⁻¹ * y⁻¹ ∉ pCoreOf 2 Y

@[expose] def FactL4L5 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (k : ℕ), (k = 4 ∨ k = 5) →
    StatedClassicalModel Q .PSL k 2 1 →
    ∀ (A S : Subgroup (MulAut Q)) (Y : Subgroup Q), (∀ q : Q, MulAut.conj q ∈ A) →
      IsSylowTwoOf S A → Y = oTwoUpper Y → (∀ α ∈ S, ∀ y ∈ Y, α y ∈ Y) →
      (∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) → (pCoreOf 2 Y).relIndex Y = 9 →
      (∃ α ∈ S, ∃ β ∈ S, ∃ y ∈ Y, (α * β) y * ((β * α) y)⁻¹ ∉ pCoreOf 2 Y) →
      A = ⊤

end CFSG.Quasithin.Vol2.Ch10.SecB

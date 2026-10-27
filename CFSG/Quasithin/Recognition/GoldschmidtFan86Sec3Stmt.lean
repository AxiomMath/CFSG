module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Arcs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T
open scoped Pointwise

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan32 (_ : FanTree Γ G) : Prop :=
  ∀ α β : V, Γ.Adj α β → ∀ x ∈ MulAction.stabilizer G α, orderOf x = valence Γ α →
    ((∃ H : Subgroup G, (H : Set G) = (Subgroup.zpowers x : Set G) * (nbrStab Γ G β : Set G)) ↔
      PClosed Γ G α)

@[expose] def Fan33ii (Γ : SimpleGraph V) (α β : V) (x : G) : Prop :=
  ∃ U : Subgroup G, U ≤ MulAction.stabilizer G α ∧
    (U.subgroupOf (MulAction.stabilizer G α)).Normal ∧ U ≤ nbrStab Γ G β ∧
    ∀ g ∈ nbrStab Γ G α, x * g * x⁻¹ * g⁻¹ ∈ U

@[expose] def Fan33 (_ : FanTree Γ G) : Prop :=
  ∀ α β : V, Γ.Adj α β → ∀ x ∈ MulAction.stabilizer G α, orderOf x = valence Γ α →
    (nbrStab Γ G α ⊓ nbrStab Γ G β = ballStab Γ G 2 α ↔ Fan33ii Γ α β x) ∧
    (Fan33ii Γ α β x ↔ PClosed Γ G α) ∧ (PClosed Γ G α → SingLe Γ G 3)

@[expose] def Fan34 (_ : FanTree Γ G) : Prop :=
  ∀ P : Arc Γ 2, (LeftSingular Γ G P.vert 0 2 ∨ RightSingular Γ G P.vert 0 2) →
    nbrStab Γ G (P.vert 1) = ballStab Γ G 2 (P.vert 1) ∧ PClosed Γ G (P.vert 1)

@[expose] def Fan35 (_ : FanTree Γ G) : Prop :=
  SingLe Γ G 3 → ¬ SingLe Γ G 2 → ∃ α : V, PClosed Γ G α

@[expose] def Fan36 (_ : FanTree Γ G) : Prop :=
  SingGe Γ G 4 → ∀ P : Arc Γ 6, valence Γ (P.vert 1) ≠ 3 →
    ¬ (LeftSingular Γ G P.vert 1 5 ∧
        ∃ g ∈ MulAction.stabilizer G (P.vert 1) ⊓ MulAction.stabilizer G (P.vert 2),
          g ∉ Gcirc Γ G (P.vert 1) (P.vert 2)) ∧
    ¬ (LeftSingular Γ G P.vert 1 5 ∧ RightSingular Γ G P.vert 1 5) ∧
    ¬ (LeftSingular Γ G P.vert 2 6 ∧ RightSingular Γ G P.vert 0 4)

@[expose] def Fan40 (_ : FanTree Γ G) : Prop := SingGe Γ G 4

end CFSG.Quasithin.Fan86

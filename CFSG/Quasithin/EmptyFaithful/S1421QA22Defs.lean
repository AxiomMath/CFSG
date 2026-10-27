module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

@[expose] def InvFiveFree (Y : Type) [Group Y] : Prop :=
  ∀ t g : Y, t ≠ 1 → t * t = 1 → orderOf g = 5 → t * g ≠ g * t

@[expose] def InvCentSolvable (Y : Type) [Group Y] : Prop :=
  ∀ t : Y, t ≠ 1 → t * t = 1 → Group.IsSolvable ↥(Subgroup.centralizer ({t} : Set Y))

@[expose] def L3InvCentSolvable : Prop :=
  ∀ (n : ℕ) (Y : Type) [Group Y] [Finite Y], 1 ≤ n → (IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y) →
    InvCentSolvable Y

@[expose] def M22InvFiveFree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSporadic .M22 Y → InvFiveFree Y

@[expose] def M23InvFiveFree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSporadic .M23 Y → InvFiveFree Y

end CFSG.Quasithin

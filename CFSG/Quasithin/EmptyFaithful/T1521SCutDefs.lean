module

public import CFSG.Quasithin.EmptyFaithful.T1515Concl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def TypeCutBlock1521 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsShort2 L →
    (IsAltType L 5 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
    ¬ (IsAlt 7 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
        IsPSL 3 2 1 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
        IsAlt 6 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
        IsPSU 3 3 1 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) ∧
    ¬ (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L))

@[expose] def TypeCutComp1521 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    (IsBender1516 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ (∃ n : ℕ, IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      ∃ n : ℕ, IsPSp4 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) →
    ¬ ((IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) ∨
      (IsSporadic .M11 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .M12 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
        IsSporadic .M22 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .M23 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
        IsSporadic .M24 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .J2 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
        IsSporadic .HS (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .He (↥L ⧸ CFSG.pCore 2 ↥L) ∨
        IsSporadic .Ru (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      (IsPSL 4 2 1 ↥L ∨ IsPSL 5 2 1 ↥L))

end CFSG.Quasithin

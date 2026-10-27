module

public import CFSG.Quasithin.Vol2.Ch11SecE42Defs
public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def A312List11Fact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (B L : Subgroup Y) (X : Type) [Group X] (n : ℕ), 2 ≤ n →
    Nonempty (ModO2 B ≃* X) → (List11_1_1Two X n ∨ (n = 2 ∧ List11_1_1Three X)) →
    ¬ A36Case4 X → ¬ IsSL2pE X → (A312Case B L ∨ A312Nonquasi B L) →
    n = 2 ∧ (IsSporadic .M23 ↥L ∨ IsSporadic .J4 ↥L ∨
      (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (IsPSL 2 p 2 ↥L ∨ IsPSL 3 p 1 ↥L ∨ IsSL3 p ↥L ∨
        IsPSU 3 p 1 ↥L ∨ IsSU3 p ↥L)) ∨
      (⁅(CFSG.oddCore ↥L).map L.subtype, L⁆ ≠ ⊥ ∧ L = B ⊔ (CFSG.oddCore ↥L).map L.subtype))

@[expose] def List701Excl (Y : Type) [Group Y] : Prop :=
  (∃ m : ℕ, LieModel Y .PSL 2 2 m) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ), Nat.card K = 2 ^ m ∧
    (Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∨ Nonempty (Y ≃* ↥(StatedSp 2 K)) ∨
      Nonempty (Y ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∨
      ∃ π : ↥(StatedSL 2 K) →* Y, Function.Surjective π)) ∨
  Nonempty (Y ≃* alternatingGroup (Fin 5)) ∨ Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (Y ≃* alternatingGroup (Fin 7)) ∨
  (Group.IsPerfect Y ∧ Nat.card (Subgroup.center Y) = 3 ∧
    Nonempty (Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 6))) ∨
  Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
  Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
  Nonempty (Y ≃* ↥NativeSporadic.M24)

@[expose] def FactM23J4 : Prop :=
  ∀ (X : Type) [Group X], (IsSporadic .M23 X ∨ IsSporadic .J4 X) →
    IsSimpleGroup X ∧ ¬ List701Excl X

structure Facts42S1 : Prop where
  list11 : A312List11Fact
  m23j4 : FactM23J4

end CFSG.Quasithin.Vol2.Ch11.SecE

module

public import CFSG.Quasithin.Background.C3Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def IsNaturalL2Prime {G : Type} [Group G] (n : ℕ) (L V : Subgroup G) : Prop :=
  (1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      IsNaturalSection L ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G))
        ((L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L) (StatedSL 2 F)) ∨
    (n = 1 ∧ ∃ Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)), Nat.card Γ = 3 ∧
      IsNaturalSection L ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G))
        ((L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L) Γ)

end CFSG.Quasithin
